import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw38912 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38912Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38912step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw38912step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw38912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38912 raw38912Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw38912 raw38912Labels = mixedMoment B raw38912step0 raw38912step0Labels := by
      have ha : raw38912step0 = (fun i j => raw38912 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38912step0 raw38912; decide +kernel
      have hl : raw38912step0Labels = raw38912Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38912 raw38912Labels permutation38 permutation7
    mixedMoment B raw38912step0 raw38912step0Labels = mixedMoment B raw38912step1 raw38912step1Labels := by
      have ha : raw38912step1 = -raw38912step0 := by apply Matrix.ext; change ∀ i j, raw38912step1 i j = -(raw38912step0 i j); unfold raw38912step1 raw38912step0; decide +kernel
      have hl : raw38912step1Labels = raw38912step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38912step1 raw38912step1Labels = mixedMoment B raw38912step2 raw38912step2Labels := by
      have ha : raw38912step2 = raw38912step1 := by apply Matrix.ext; unfold raw38912step2 raw38912step1; decide +kernel
      have hl : raw38912step1Labels = labelEmbedding4 ∘ raw38912step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38912step1 raw38912step1Labels raw38912step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw38913 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38913Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38913step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38913 raw38913Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw38913 raw38913Labels = mixedMoment B raw38913step0 raw38913step0Labels := by
      have ha : raw38913step0 = raw38913 := by apply Matrix.ext; unfold raw38913step0 raw38913; decide +kernel
      have hl : raw38913Labels = labelEmbedding2 ∘ raw38913step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38913 raw38913Labels raw38913step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw38914 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38914Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38914step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw38914step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw38914step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw38914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38914 raw38914Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw38914 raw38914Labels = mixedMoment B raw38914step0 raw38914step0Labels := by
      have ha : raw38914step0 = (fun i j => raw38914 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38914step0 raw38914; decide +kernel
      have hl : raw38914step0Labels = raw38914Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38914 raw38914Labels permutation10 permutation7
    mixedMoment B raw38914step0 raw38914step0Labels = mixedMoment B raw38914step1 raw38914step1Labels := by
      have ha : raw38914step1 = -raw38914step0 := by apply Matrix.ext; change ∀ i j, raw38914step1 i j = -(raw38914step0 i j); unfold raw38914step1 raw38914step0; decide +kernel
      have hl : raw38914step1Labels = raw38914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38914step1 raw38914step1Labels = mixedMoment B raw38914step2 raw38914step2Labels := by
      have ha : raw38914step2 = raw38914step1 := by apply Matrix.ext; unfold raw38914step2 raw38914step1; decide +kernel
      have hl : raw38914step1Labels = labelEmbedding4 ∘ raw38914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38914step1 raw38914step1Labels raw38914step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw38915 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38915Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38915 raw38915Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw38915 raw38915Labels = mixedMoment B raw38915step0 raw38915step0Labels := by
      have ha : raw38915step0 = raw38915 := by apply Matrix.ext; unfold raw38915step0 raw38915; decide +kernel
      have hl : raw38915Labels = labelEmbedding2 ∘ raw38915step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38915 raw38915Labels raw38915step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw38916 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38916Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38916step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw38916step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw38916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38916 raw38916Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw38916 raw38916Labels = mixedMoment B raw38916step0 raw38916step0Labels := by
      have ha : raw38916step0 = (fun i j => raw38916 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38916step0 raw38916; decide +kernel
      have hl : raw38916step0Labels = raw38916Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38916 raw38916Labels permutation50 permutation7
    mixedMoment B raw38916step0 raw38916step0Labels = mixedMoment B raw38916step1 raw38916step1Labels := by
      have ha : raw38916step1 = -raw38916step0 := by apply Matrix.ext; change ∀ i j, raw38916step1 i j = -(raw38916step0 i j); unfold raw38916step1 raw38916step0; decide +kernel
      have hl : raw38916step1Labels = raw38916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38916step1 raw38916step1Labels = mixedMoment B raw38916step2 raw38916step2Labels := by
      have ha : raw38916step2 = raw38916step1 := by apply Matrix.ext; unfold raw38916step2 raw38916step1; decide +kernel
      have hl : raw38916step1Labels = labelEmbedding4 ∘ raw38916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38916step1 raw38916step1Labels raw38916step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw38917 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38917Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38917 raw38917Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw38917 raw38917Labels = mixedMoment B raw38917step0 raw38917step0Labels := by
      have ha : raw38917step0 = raw38917 := by apply Matrix.ext; unfold raw38917step0 raw38917; decide +kernel
      have hl : raw38917Labels = labelEmbedding2 ∘ raw38917step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38917 raw38917Labels raw38917step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw38918 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38918Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38918step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38918step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw38918step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw38918step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38918 raw38918Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw38918 raw38918Labels = mixedMoment B raw38918step0 raw38918step0Labels := by
      have ha : raw38918step0 = (fun i j => raw38918 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38918step0 raw38918; decide +kernel
      have hl : raw38918step0Labels = raw38918Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38918 raw38918Labels permutation8 permutation7
    mixedMoment B raw38918step0 raw38918step0Labels = mixedMoment B raw38918step1 raw38918step1Labels := by
      have ha : raw38918step1 = -raw38918step0 := by apply Matrix.ext; change ∀ i j, raw38918step1 i j = -(raw38918step0 i j); unfold raw38918step1 raw38918step0; decide +kernel
      have hl : raw38918step1Labels = raw38918step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38918step1 raw38918step1Labels = mixedMoment B raw38918step2 raw38918step2Labels := by
      have ha : raw38918step2 = raw38918step1 := by apply Matrix.ext; unfold raw38918step2 raw38918step1; decide +kernel
      have hl : raw38918step1Labels = labelEmbedding4 ∘ raw38918step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38918step1 raw38918step1Labels raw38918step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw38919 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38919Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38919step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38919 raw38919Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw38919 raw38919Labels = mixedMoment B raw38919step0 raw38919step0Labels := by
      have ha : raw38919step0 = raw38919 := by apply Matrix.ext; unfold raw38919step0 raw38919; decide +kernel
      have hl : raw38919Labels = labelEmbedding2 ∘ raw38919step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38919 raw38919Labels raw38919step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw38920 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38920Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38920step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw38920step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw38920step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw38920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38920 raw38920Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw38920 raw38920Labels = mixedMoment B raw38920step0 raw38920step0Labels := by
      have ha : raw38920step0 = (fun i j => raw38920 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38920step0 raw38920; decide +kernel
      have hl : raw38920step0Labels = raw38920Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38920 raw38920Labels permutation10 permutation7
    mixedMoment B raw38920step0 raw38920step0Labels = mixedMoment B raw38920step1 raw38920step1Labels := by
      have ha : raw38920step1 = -raw38920step0 := by apply Matrix.ext; change ∀ i j, raw38920step1 i j = -(raw38920step0 i j); unfold raw38920step1 raw38920step0; decide +kernel
      have hl : raw38920step1Labels = raw38920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38920step1 raw38920step1Labels = mixedMoment B raw38920step2 raw38920step2Labels := by
      have ha : raw38920step2 = raw38920step1 := by apply Matrix.ext; unfold raw38920step2 raw38920step1; decide +kernel
      have hl : raw38920step1Labels = labelEmbedding4 ∘ raw38920step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38920step1 raw38920step1Labels raw38920step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw38921 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38921Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38921step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38921 raw38921Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw38921 raw38921Labels = mixedMoment B raw38921step0 raw38921step0Labels := by
      have ha : raw38921step0 = raw38921 := by apply Matrix.ext; unfold raw38921step0 raw38921; decide +kernel
      have hl : raw38921Labels = labelEmbedding2 ∘ raw38921step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38921 raw38921Labels raw38921step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2116 node2116Labels := by rfl

def raw38922 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38922Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38922step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38922step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw38922step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38922step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw38922step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38922 raw38922Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw38922 raw38922Labels = mixedMoment B raw38922step0 raw38922step0Labels := by
      have ha : raw38922step0 = (fun i j => raw38922 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38922step0 raw38922; decide +kernel
      have hl : raw38922step0Labels = raw38922Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38922 raw38922Labels permutation8 permutation7
    mixedMoment B raw38922step0 raw38922step0Labels = mixedMoment B raw38922step1 raw38922step1Labels := by
      have ha : raw38922step1 = -raw38922step0 := by apply Matrix.ext; change ∀ i j, raw38922step1 i j = -(raw38922step0 i j); unfold raw38922step1 raw38922step0; decide +kernel
      have hl : raw38922step1Labels = raw38922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38922step1 raw38922step1Labels = mixedMoment B raw38922step2 raw38922step2Labels := by
      have ha : raw38922step2 = raw38922step1 := by apply Matrix.ext; unfold raw38922step2 raw38922step1; decide +kernel
      have hl : raw38922step1Labels = labelEmbedding4 ∘ raw38922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38922step1 raw38922step1Labels raw38922step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

def raw38923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38923Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38923 raw38923Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw38923 raw38923Labels = mixedMoment B raw38923step0 raw38923step0Labels := by
      have ha : raw38923step0 = raw38923 := by apply Matrix.ext; unfold raw38923step0 raw38923; decide +kernel
      have hl : raw38923Labels = labelEmbedding2 ∘ raw38923step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38923 raw38923Labels raw38923step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw38924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38924Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw38924step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38924step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38924step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38924 raw38924Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw38924 raw38924Labels = mixedMoment B raw38924step0 raw38924step0Labels := by
      have ha : raw38924step0 = (fun i j => raw38924 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38924step0 raw38924; decide +kernel
      have hl : raw38924step0Labels = raw38924Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38924 raw38924Labels permutation212 permutation7
    mixedMoment B raw38924step0 raw38924step0Labels = mixedMoment B raw38924step1 raw38924step1Labels := by
      have ha : raw38924step1 = -raw38924step0 := by apply Matrix.ext; change ∀ i j, raw38924step1 i j = -(raw38924step0 i j); unfold raw38924step1 raw38924step0; decide +kernel
      have hl : raw38924step1Labels = raw38924step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38924step1 raw38924step1Labels = mixedMoment B raw38924step2 raw38924step2Labels := by
      have ha : raw38924step2 = raw38924step1 := by apply Matrix.ext; unfold raw38924step2 raw38924step1; decide +kernel
      have hl : raw38924step1Labels = labelEmbedding4 ∘ raw38924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38924step1 raw38924step1Labels raw38924step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw38925 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38925Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38925 raw38925Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw38925 raw38925Labels = mixedMoment B raw38925step0 raw38925step0Labels := by
      have ha : raw38925step0 = raw38925 := by apply Matrix.ext; unfold raw38925step0 raw38925; decide +kernel
      have hl : raw38925Labels = labelEmbedding2 ∘ raw38925step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38925 raw38925Labels raw38925step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw38926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38926Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw38926step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw38926step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38926step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw38926step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38926 raw38926Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw38926 raw38926Labels = mixedMoment B raw38926step0 raw38926step0Labels := by
      have ha : raw38926step0 = (fun i j => raw38926 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38926step0 raw38926; decide +kernel
      have hl : raw38926step0Labels = raw38926Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38926 raw38926Labels permutation44 permutation7
    mixedMoment B raw38926step0 raw38926step0Labels = mixedMoment B raw38926step1 raw38926step1Labels := by
      have ha : raw38926step1 = -raw38926step0 := by apply Matrix.ext; change ∀ i j, raw38926step1 i j = -(raw38926step0 i j); unfold raw38926step1 raw38926step0; decide +kernel
      have hl : raw38926step1Labels = raw38926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38926step1 raw38926step1Labels = mixedMoment B raw38926step2 raw38926step2Labels := by
      have ha : raw38926step2 = raw38926step1 := by apply Matrix.ext; unfold raw38926step2 raw38926step1; decide +kernel
      have hl : raw38926step1Labels = labelEmbedding4 ∘ raw38926step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38926step1 raw38926step1Labels raw38926step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw38927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38927Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38927 raw38927Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw38927 raw38927Labels = mixedMoment B raw38927step0 raw38927step0Labels := by
      have ha : raw38927step0 = raw38927 := by apply Matrix.ext; unfold raw38927step0 raw38927; decide +kernel
      have hl : raw38927Labels = labelEmbedding2 ∘ raw38927step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38927 raw38927Labels raw38927step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw38928 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38928Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw38928step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38928step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38928step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38928 raw38928Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw38928 raw38928Labels = mixedMoment B raw38928step0 raw38928step0Labels := by
      have ha : raw38928step0 = (fun i j => raw38928 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38928step0 raw38928; decide +kernel
      have hl : raw38928step0Labels = raw38928Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38928 raw38928Labels permutation50 permutation7
    mixedMoment B raw38928step0 raw38928step0Labels = mixedMoment B raw38928step1 raw38928step1Labels := by
      have ha : raw38928step1 = -raw38928step0 := by apply Matrix.ext; change ∀ i j, raw38928step1 i j = -(raw38928step0 i j); unfold raw38928step1 raw38928step0; decide +kernel
      have hl : raw38928step1Labels = raw38928step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38928step1 raw38928step1Labels = mixedMoment B raw38928step2 raw38928step2Labels := by
      have ha : raw38928step2 = raw38928step1 := by apply Matrix.ext; unfold raw38928step2 raw38928step1; decide +kernel
      have hl : raw38928step1Labels = labelEmbedding4 ∘ raw38928step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38928step1 raw38928step1Labels raw38928step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw38929 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw38929Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38929step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw38929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38929 raw38929Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw38929 raw38929Labels = mixedMoment B raw38929step0 raw38929step0Labels := by
      have ha : raw38929step0 = raw38929 := by apply Matrix.ext; unfold raw38929step0 raw38929; decide +kernel
      have hl : raw38929Labels = labelEmbedding2 ∘ raw38929step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38929 raw38929Labels raw38929step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw38930 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw38930Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38930step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw38930step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw38930step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw38930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38930 raw38930Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw38930 raw38930Labels = mixedMoment B raw38930step0 raw38930step0Labels := by
      have ha : raw38930step0 = (fun i j => raw38930 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38930step0 raw38930; decide +kernel
      have hl : raw38930step0Labels = raw38930Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38930 raw38930Labels permutation8 permutation7
    mixedMoment B raw38930step0 raw38930step0Labels = mixedMoment B raw38930step1 raw38930step1Labels := by
      have ha : raw38930step1 = -raw38930step0 := by apply Matrix.ext; change ∀ i j, raw38930step1 i j = -(raw38930step0 i j); unfold raw38930step1 raw38930step0; decide +kernel
      have hl : raw38930step1Labels = raw38930step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38930step1 raw38930step1Labels = mixedMoment B raw38930step2 raw38930step2Labels := by
      have ha : raw38930step2 = raw38930step1 := by apply Matrix.ext; unfold raw38930step2 raw38930step1; decide +kernel
      have hl : raw38930step1Labels = labelEmbedding4 ∘ raw38930step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38930step1 raw38930step1Labels raw38930step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw38931 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38931Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38931step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38931 raw38931Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw38931 raw38931Labels = mixedMoment B raw38931step0 raw38931step0Labels := by
      have ha : raw38931step0 = raw38931 := by apply Matrix.ext; unfold raw38931step0 raw38931; decide +kernel
      have hl : raw38931Labels = labelEmbedding2 ∘ raw38931step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38931 raw38931Labels raw38931step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw38932 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38932Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38932step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw38932step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw38932step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw38932step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38932 raw38932Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw38932 raw38932Labels = mixedMoment B raw38932step0 raw38932step0Labels := by
      have ha : raw38932step0 = (fun i j => raw38932 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38932step0 raw38932; decide +kernel
      have hl : raw38932step0Labels = raw38932Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38932 raw38932Labels permutation12 permutation7
    mixedMoment B raw38932step0 raw38932step0Labels = mixedMoment B raw38932step1 raw38932step1Labels := by
      have ha : raw38932step1 = -raw38932step0 := by apply Matrix.ext; change ∀ i j, raw38932step1 i j = -(raw38932step0 i j); unfold raw38932step1 raw38932step0; decide +kernel
      have hl : raw38932step1Labels = raw38932step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38932step1 raw38932step1Labels = mixedMoment B raw38932step2 raw38932step2Labels := by
      have ha : raw38932step2 = raw38932step1 := by apply Matrix.ext; unfold raw38932step2 raw38932step1; decide +kernel
      have hl : raw38932step1Labels = labelEmbedding4 ∘ raw38932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38932step1 raw38932step1Labels raw38932step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw38933 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw38933Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38933step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw38933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38933 raw38933Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw38933 raw38933Labels = mixedMoment B raw38933step0 raw38933step0Labels := by
      have ha : raw38933step0 = raw38933 := by apply Matrix.ext; unfold raw38933step0 raw38933; decide +kernel
      have hl : raw38933Labels = labelEmbedding2 ∘ raw38933step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38933 raw38933Labels raw38933step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw38934 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw38934Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38934step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw38934step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw38934step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw38934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38934 raw38934Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw38934 raw38934Labels = mixedMoment B raw38934step0 raw38934step0Labels := by
      have ha : raw38934step0 = (fun i j => raw38934 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38934step0 raw38934; decide +kernel
      have hl : raw38934step0Labels = raw38934Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38934 raw38934Labels permutation13 permutation7
    mixedMoment B raw38934step0 raw38934step0Labels = mixedMoment B raw38934step1 raw38934step1Labels := by
      have ha : raw38934step1 = -raw38934step0 := by apply Matrix.ext; change ∀ i j, raw38934step1 i j = -(raw38934step0 i j); unfold raw38934step1 raw38934step0; decide +kernel
      have hl : raw38934step1Labels = raw38934step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38934step1 raw38934step1Labels = mixedMoment B raw38934step2 raw38934step2Labels := by
      have ha : raw38934step2 = raw38934step1 := by apply Matrix.ext; unfold raw38934step2 raw38934step1; decide +kernel
      have hl : raw38934step1Labels = labelEmbedding4 ∘ raw38934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38934step1 raw38934step1Labels raw38934step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw38935 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw38935Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38935step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw38935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38935 raw38935Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw38935 raw38935Labels = mixedMoment B raw38935step0 raw38935step0Labels := by
      have ha : raw38935step0 = raw38935 := by apply Matrix.ext; unfold raw38935step0 raw38935; decide +kernel
      have hl : raw38935Labels = labelEmbedding2 ∘ raw38935step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38935 raw38935Labels raw38935step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw38936 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw38936Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38936step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw38936step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38936step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw38936step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38936step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw38936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38936 raw38936Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw38936 raw38936Labels = mixedMoment B raw38936step0 raw38936step0Labels := by
      have ha : raw38936step0 = (fun i j => raw38936 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38936step0 raw38936; decide +kernel
      have hl : raw38936step0Labels = raw38936Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38936 raw38936Labels permutation3 permutation7
    mixedMoment B raw38936step0 raw38936step0Labels = mixedMoment B raw38936step1 raw38936step1Labels := by
      have ha : raw38936step1 = -raw38936step0 := by apply Matrix.ext; change ∀ i j, raw38936step1 i j = -(raw38936step0 i j); unfold raw38936step1 raw38936step0; decide +kernel
      have hl : raw38936step1Labels = raw38936step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38936step1 raw38936step1Labels = mixedMoment B raw38936step2 raw38936step2Labels := by
      have ha : raw38936step2 = raw38936step1 := by apply Matrix.ext; unfold raw38936step2 raw38936step1; decide +kernel
      have hl : raw38936step1Labels = labelEmbedding4 ∘ raw38936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38936step1 raw38936step1Labels raw38936step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw38937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38937Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38937 raw38937Labels = mixedMoment B node2295 node2295Labels := by
  calc
    mixedMoment B raw38937 raw38937Labels = mixedMoment B raw38937step0 raw38937step0Labels := by
      have ha : raw38937step0 = raw38937 := by apply Matrix.ext; unfold raw38937step0 raw38937; decide +kernel
      have hl : raw38937Labels = labelEmbedding2 ∘ raw38937step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38937 raw38937Labels raw38937step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2295 node2295Labels := by rfl

def raw38938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38938Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw38938step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38938step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38938step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38938 raw38938Labels = mixedMoment B node3315 node3315Labels := by
  calc
    mixedMoment B raw38938 raw38938Labels = mixedMoment B raw38938step0 raw38938step0Labels := by
      have ha : raw38938step0 = (fun i j => raw38938 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38938step0 raw38938; decide +kernel
      have hl : raw38938step0Labels = raw38938Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38938 raw38938Labels permutation158 permutation7
    mixedMoment B raw38938step0 raw38938step0Labels = mixedMoment B raw38938step1 raw38938step1Labels := by
      have ha : raw38938step1 = -raw38938step0 := by apply Matrix.ext; change ∀ i j, raw38938step1 i j = -(raw38938step0 i j); unfold raw38938step1 raw38938step0; decide +kernel
      have hl : raw38938step1Labels = raw38938step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38938step1 raw38938step1Labels = mixedMoment B raw38938step2 raw38938step2Labels := by
      have ha : raw38938step2 = raw38938step1 := by apply Matrix.ext; unfold raw38938step2 raw38938step1; decide +kernel
      have hl : raw38938step1Labels = labelEmbedding4 ∘ raw38938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38938step1 raw38938step1Labels raw38938step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3315 node3315Labels := by rfl

def raw38939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38939Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38939 raw38939Labels = mixedMoment B node2296 node2296Labels := by
  calc
    mixedMoment B raw38939 raw38939Labels = mixedMoment B raw38939step0 raw38939step0Labels := by
      have ha : raw38939step0 = raw38939 := by apply Matrix.ext; unfold raw38939step0 raw38939; decide +kernel
      have hl : raw38939Labels = labelEmbedding2 ∘ raw38939step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38939 raw38939Labels raw38939step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2296 node2296Labels := by rfl

def raw38940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38940Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw38940step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38940step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38940step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38940 raw38940Labels = mixedMoment B node3316 node3316Labels := by
  calc
    mixedMoment B raw38940 raw38940Labels = mixedMoment B raw38940step0 raw38940step0Labels := by
      have ha : raw38940step0 = (fun i j => raw38940 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38940step0 raw38940; decide +kernel
      have hl : raw38940step0Labels = raw38940Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38940 raw38940Labels permutation158 permutation7
    mixedMoment B raw38940step0 raw38940step0Labels = mixedMoment B raw38940step1 raw38940step1Labels := by
      have ha : raw38940step1 = -raw38940step0 := by apply Matrix.ext; change ∀ i j, raw38940step1 i j = -(raw38940step0 i j); unfold raw38940step1 raw38940step0; decide +kernel
      have hl : raw38940step1Labels = raw38940step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38940step1 raw38940step1Labels = mixedMoment B raw38940step2 raw38940step2Labels := by
      have ha : raw38940step2 = raw38940step1 := by apply Matrix.ext; unfold raw38940step2 raw38940step1; decide +kernel
      have hl : raw38940step1Labels = labelEmbedding4 ∘ raw38940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38940step1 raw38940step1Labels raw38940step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3316 node3316Labels := by rfl

def raw38941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38941Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38941step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38941 raw38941Labels = mixedMoment B node2297 node2297Labels := by
  calc
    mixedMoment B raw38941 raw38941Labels = mixedMoment B raw38941step0 raw38941step0Labels := by
      have ha : raw38941step0 = raw38941 := by apply Matrix.ext; unfold raw38941step0 raw38941; decide +kernel
      have hl : raw38941Labels = labelEmbedding2 ∘ raw38941step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38941 raw38941Labels raw38941step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2297 node2297Labels := by rfl

def raw38942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38942Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38942step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38942step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38942step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38942 raw38942Labels = mixedMoment B node3323 node3323Labels := by
  calc
    mixedMoment B raw38942 raw38942Labels = mixedMoment B raw38942step0 raw38942step0Labels := by
      have ha : raw38942step0 = (fun i j => raw38942 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38942step0 raw38942; decide +kernel
      have hl : raw38942step0Labels = raw38942Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38942 raw38942Labels permutation152 permutation7
    mixedMoment B raw38942step0 raw38942step0Labels = mixedMoment B raw38942step1 raw38942step1Labels := by
      have ha : raw38942step1 = -raw38942step0 := by apply Matrix.ext; change ∀ i j, raw38942step1 i j = -(raw38942step0 i j); unfold raw38942step1 raw38942step0; decide +kernel
      have hl : raw38942step1Labels = raw38942step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38942step1 raw38942step1Labels = mixedMoment B raw38942step2 raw38942step2Labels := by
      have ha : raw38942step2 = raw38942step1 := by apply Matrix.ext; unfold raw38942step2 raw38942step1; decide +kernel
      have hl : raw38942step1Labels = labelEmbedding4 ∘ raw38942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38942step1 raw38942step1Labels raw38942step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3323 node3323Labels := by rfl

def raw38943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38943Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38943 raw38943Labels = mixedMoment B node2298 node2298Labels := by
  calc
    mixedMoment B raw38943 raw38943Labels = mixedMoment B raw38943step0 raw38943step0Labels := by
      have ha : raw38943step0 = raw38943 := by apply Matrix.ext; unfold raw38943step0 raw38943; decide +kernel
      have hl : raw38943Labels = labelEmbedding2 ∘ raw38943step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38943 raw38943Labels raw38943step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2298 node2298Labels := by rfl

def raw38944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38944Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw38944step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38944step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38944step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38944 raw38944Labels = mixedMoment B node3320 node3320Labels := by
  calc
    mixedMoment B raw38944 raw38944Labels = mixedMoment B raw38944step0 raw38944step0Labels := by
      have ha : raw38944step0 = (fun i j => raw38944 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38944step0 raw38944; decide +kernel
      have hl : raw38944step0Labels = raw38944Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38944 raw38944Labels permutation164 permutation7
    mixedMoment B raw38944step0 raw38944step0Labels = mixedMoment B raw38944step1 raw38944step1Labels := by
      have ha : raw38944step1 = -raw38944step0 := by apply Matrix.ext; change ∀ i j, raw38944step1 i j = -(raw38944step0 i j); unfold raw38944step1 raw38944step0; decide +kernel
      have hl : raw38944step1Labels = raw38944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38944step1 raw38944step1Labels = mixedMoment B raw38944step2 raw38944step2Labels := by
      have ha : raw38944step2 = raw38944step1 := by apply Matrix.ext; unfold raw38944step2 raw38944step1; decide +kernel
      have hl : raw38944step1Labels = labelEmbedding4 ∘ raw38944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38944step1 raw38944step1Labels raw38944step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3320 node3320Labels := by rfl

def raw38945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38945Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38945 raw38945Labels = mixedMoment B node2299 node2299Labels := by
  calc
    mixedMoment B raw38945 raw38945Labels = mixedMoment B raw38945step0 raw38945step0Labels := by
      have ha : raw38945step0 = raw38945 := by apply Matrix.ext; unfold raw38945step0 raw38945; decide +kernel
      have hl : raw38945Labels = labelEmbedding2 ∘ raw38945step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38945 raw38945Labels raw38945step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2299 node2299Labels := by rfl

def raw38946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38946Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38946step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38946step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38946 raw38946Labels = mixedMoment B node3324 node3324Labels := by
  calc
    mixedMoment B raw38946 raw38946Labels = mixedMoment B raw38946step0 raw38946step0Labels := by
      have ha : raw38946step0 = (fun i j => raw38946 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38946step0 raw38946; decide +kernel
      have hl : raw38946step0Labels = raw38946Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38946 raw38946Labels permutation152 permutation7
    mixedMoment B raw38946step0 raw38946step0Labels = mixedMoment B raw38946step1 raw38946step1Labels := by
      have ha : raw38946step1 = -raw38946step0 := by apply Matrix.ext; change ∀ i j, raw38946step1 i j = -(raw38946step0 i j); unfold raw38946step1 raw38946step0; decide +kernel
      have hl : raw38946step1Labels = raw38946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38946step1 raw38946step1Labels = mixedMoment B raw38946step2 raw38946step2Labels := by
      have ha : raw38946step2 = raw38946step1 := by apply Matrix.ext; unfold raw38946step2 raw38946step1; decide +kernel
      have hl : raw38946step1Labels = labelEmbedding4 ∘ raw38946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38946step1 raw38946step1Labels raw38946step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3324 node3324Labels := by rfl

def raw38947 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38947Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38947 raw38947Labels = mixedMoment B node2300 node2300Labels := by
  calc
    mixedMoment B raw38947 raw38947Labels = mixedMoment B raw38947step0 raw38947step0Labels := by
      have ha : raw38947step0 = raw38947 := by apply Matrix.ext; unfold raw38947step0 raw38947; decide +kernel
      have hl : raw38947Labels = labelEmbedding2 ∘ raw38947step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38947 raw38947Labels raw38947step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2300 node2300Labels := by rfl

def raw38948 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38948Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw38948step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38948step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38948 raw38948Labels = mixedMoment B node3325 node3325Labels := by
  calc
    mixedMoment B raw38948 raw38948Labels = mixedMoment B raw38948step0 raw38948step0Labels := by
      have ha : raw38948step0 = (fun i j => raw38948 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38948step0 raw38948; decide +kernel
      have hl : raw38948step0Labels = raw38948Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38948 raw38948Labels permutation32 permutation7
    mixedMoment B raw38948step0 raw38948step0Labels = mixedMoment B raw38948step1 raw38948step1Labels := by
      have ha : raw38948step1 = -raw38948step0 := by apply Matrix.ext; change ∀ i j, raw38948step1 i j = -(raw38948step0 i j); unfold raw38948step1 raw38948step0; decide +kernel
      have hl : raw38948step1Labels = raw38948step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38948step1 raw38948step1Labels = mixedMoment B raw38948step2 raw38948step2Labels := by
      have ha : raw38948step2 = raw38948step1 := by apply Matrix.ext; unfold raw38948step2 raw38948step1; decide +kernel
      have hl : raw38948step1Labels = labelEmbedding4 ∘ raw38948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38948step1 raw38948step1Labels raw38948step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3325 node3325Labels := by rfl

def raw38949 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38949Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38949 raw38949Labels = mixedMoment B node2301 node2301Labels := by
  calc
    mixedMoment B raw38949 raw38949Labels = mixedMoment B raw38949step0 raw38949step0Labels := by
      have ha : raw38949step0 = raw38949 := by apply Matrix.ext; unfold raw38949step0 raw38949; decide +kernel
      have hl : raw38949Labels = labelEmbedding2 ∘ raw38949step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38949 raw38949Labels raw38949step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2301 node2301Labels := by rfl

def raw38950 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38950Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw38950step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38950step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38950 raw38950Labels = mixedMoment B node3326 node3326Labels := by
  calc
    mixedMoment B raw38950 raw38950Labels = mixedMoment B raw38950step0 raw38950step0Labels := by
      have ha : raw38950step0 = (fun i j => raw38950 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38950step0 raw38950; decide +kernel
      have hl : raw38950step0Labels = raw38950Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38950 raw38950Labels permutation33 permutation7
    mixedMoment B raw38950step0 raw38950step0Labels = mixedMoment B raw38950step1 raw38950step1Labels := by
      have ha : raw38950step1 = -raw38950step0 := by apply Matrix.ext; change ∀ i j, raw38950step1 i j = -(raw38950step0 i j); unfold raw38950step1 raw38950step0; decide +kernel
      have hl : raw38950step1Labels = raw38950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38950step1 raw38950step1Labels = mixedMoment B raw38950step2 raw38950step2Labels := by
      have ha : raw38950step2 = raw38950step1 := by apply Matrix.ext; unfold raw38950step2 raw38950step1; decide +kernel
      have hl : raw38950step1Labels = labelEmbedding4 ∘ raw38950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38950step1 raw38950step1Labels raw38950step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3326 node3326Labels := by rfl

def raw38951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38951Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38951 raw38951Labels = mixedMoment B node2302 node2302Labels := by
  calc
    mixedMoment B raw38951 raw38951Labels = mixedMoment B raw38951step0 raw38951step0Labels := by
      have ha : raw38951step0 = raw38951 := by apply Matrix.ext; unfold raw38951step0 raw38951; decide +kernel
      have hl : raw38951Labels = labelEmbedding2 ∘ raw38951step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38951 raw38951Labels raw38951step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2302 node2302Labels := by rfl

def raw38952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38952Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38952step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38952 raw38952Labels = mixedMoment B node2448 node2448Labels := by
  calc
    mixedMoment B raw38952 raw38952Labels = mixedMoment B raw38952step0 raw38952step0Labels := by
      have ha : raw38952step0 = (fun i j => raw38952 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38952step0 raw38952; decide +kernel
      have hl : raw38952step0Labels = raw38952Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38952 raw38952Labels permutation682 permutation7
    mixedMoment B raw38952step0 raw38952step0Labels = mixedMoment B raw38952step1 raw38952step1Labels := by
      have ha : raw38952step1 = raw38952step0 := by apply Matrix.ext; unfold raw38952step1 raw38952step0; decide +kernel
      have hl : raw38952step0Labels = labelEmbedding4 ∘ raw38952step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38952step0 raw38952step0Labels raw38952step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2448 node2448Labels := by rfl

def raw38953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38953Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38953 raw38953Labels = mixedMoment B node2303 node2303Labels := by
  calc
    mixedMoment B raw38953 raw38953Labels = mixedMoment B raw38953step0 raw38953step0Labels := by
      have ha : raw38953step0 = raw38953 := by apply Matrix.ext; unfold raw38953step0 raw38953; decide +kernel
      have hl : raw38953Labels = labelEmbedding2 ∘ raw38953step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38953 raw38953Labels raw38953step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2303 node2303Labels := by rfl

def raw38954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38954Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw38954step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38954step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38954step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38954 raw38954Labels = mixedMoment B node3314 node3314Labels := by
  calc
    mixedMoment B raw38954 raw38954Labels = mixedMoment B raw38954step0 raw38954step0Labels := by
      have ha : raw38954step0 = (fun i j => raw38954 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38954step0 raw38954; decide +kernel
      have hl : raw38954step0Labels = raw38954Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38954 raw38954Labels permutation152 permutation7
    mixedMoment B raw38954step0 raw38954step0Labels = mixedMoment B raw38954step1 raw38954step1Labels := by
      have ha : raw38954step1 = -raw38954step0 := by apply Matrix.ext; change ∀ i j, raw38954step1 i j = -(raw38954step0 i j); unfold raw38954step1 raw38954step0; decide +kernel
      have hl : raw38954step1Labels = raw38954step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38954step1 raw38954step1Labels = mixedMoment B raw38954step2 raw38954step2Labels := by
      have ha : raw38954step2 = raw38954step1 := by apply Matrix.ext; unfold raw38954step2 raw38954step1; decide +kernel
      have hl : raw38954step1Labels = labelEmbedding4 ∘ raw38954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38954step1 raw38954step1Labels raw38954step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3314 node3314Labels := by rfl

def raw38955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38955Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38955 raw38955Labels = mixedMoment B node2305 node2305Labels := by
  calc
    mixedMoment B raw38955 raw38955Labels = mixedMoment B raw38955step0 raw38955step0Labels := by
      have ha : raw38955step0 = raw38955 := by apply Matrix.ext; unfold raw38955step0 raw38955; decide +kernel
      have hl : raw38955Labels = labelEmbedding2 ∘ raw38955step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38955 raw38955Labels raw38955step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2305 node2305Labels := by rfl

def raw38956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38956Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw38956step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38956step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38956 raw38956Labels = mixedMoment B node3317 node3317Labels := by
  calc
    mixedMoment B raw38956 raw38956Labels = mixedMoment B raw38956step0 raw38956step0Labels := by
      have ha : raw38956step0 = (fun i j => raw38956 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38956step0 raw38956; decide +kernel
      have hl : raw38956step0Labels = raw38956Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38956 raw38956Labels permutation153 permutation7
    mixedMoment B raw38956step0 raw38956step0Labels = mixedMoment B raw38956step1 raw38956step1Labels := by
      have ha : raw38956step1 = -raw38956step0 := by apply Matrix.ext; change ∀ i j, raw38956step1 i j = -(raw38956step0 i j); unfold raw38956step1 raw38956step0; decide +kernel
      have hl : raw38956step1Labels = raw38956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38956step1 raw38956step1Labels = mixedMoment B raw38956step2 raw38956step2Labels := by
      have ha : raw38956step2 = raw38956step1 := by apply Matrix.ext; unfold raw38956step2 raw38956step1; decide +kernel
      have hl : raw38956step1Labels = labelEmbedding4 ∘ raw38956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38956step1 raw38956step1Labels raw38956step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3317 node3317Labels := by rfl

def raw38957 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38957Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38957step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38957 raw38957Labels = mixedMoment B node2306 node2306Labels := by
  calc
    mixedMoment B raw38957 raw38957Labels = mixedMoment B raw38957step0 raw38957step0Labels := by
      have ha : raw38957step0 = raw38957 := by apply Matrix.ext; unfold raw38957step0 raw38957; decide +kernel
      have hl : raw38957Labels = labelEmbedding2 ∘ raw38957step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38957 raw38957Labels raw38957step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2306 node2306Labels := by rfl

def raw38958 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38958Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw38958step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38958step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38958 raw38958Labels = mixedMoment B node3318 node3318Labels := by
  calc
    mixedMoment B raw38958 raw38958Labels = mixedMoment B raw38958step0 raw38958step0Labels := by
      have ha : raw38958step0 = (fun i j => raw38958 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38958step0 raw38958; decide +kernel
      have hl : raw38958step0Labels = raw38958Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38958 raw38958Labels permutation32 permutation7
    mixedMoment B raw38958step0 raw38958step0Labels = mixedMoment B raw38958step1 raw38958step1Labels := by
      have ha : raw38958step1 = -raw38958step0 := by apply Matrix.ext; change ∀ i j, raw38958step1 i j = -(raw38958step0 i j); unfold raw38958step1 raw38958step0; decide +kernel
      have hl : raw38958step1Labels = raw38958step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38958step1 raw38958step1Labels = mixedMoment B raw38958step2 raw38958step2Labels := by
      have ha : raw38958step2 = raw38958step1 := by apply Matrix.ext; unfold raw38958step2 raw38958step1; decide +kernel
      have hl : raw38958step1Labels = labelEmbedding4 ∘ raw38958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38958step1 raw38958step1Labels raw38958step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3318 node3318Labels := by rfl

def raw38959 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38959Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38959 raw38959Labels = mixedMoment B node2307 node2307Labels := by
  calc
    mixedMoment B raw38959 raw38959Labels = mixedMoment B raw38959step0 raw38959step0Labels := by
      have ha : raw38959step0 = raw38959 := by apply Matrix.ext; unfold raw38959step0 raw38959; decide +kernel
      have hl : raw38959Labels = labelEmbedding2 ∘ raw38959step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38959 raw38959Labels raw38959step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2307 node2307Labels := by rfl

def raw38960 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38960Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38960step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38960 raw38960Labels = mixedMoment B node2376 node2376Labels := by
  calc
    mixedMoment B raw38960 raw38960Labels = mixedMoment B raw38960step0 raw38960step0Labels := by
      have ha : raw38960step0 = (fun i j => raw38960 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38960step0 raw38960; decide +kernel
      have hl : raw38960step0Labels = raw38960Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38960 raw38960Labels permutation151 permutation7
    mixedMoment B raw38960step0 raw38960step0Labels = mixedMoment B raw38960step1 raw38960step1Labels := by
      have ha : raw38960step1 = raw38960step0 := by apply Matrix.ext; unfold raw38960step1 raw38960step0; decide +kernel
      have hl : raw38960step0Labels = labelEmbedding4 ∘ raw38960step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38960step0 raw38960step0Labels raw38960step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2376 node2376Labels := by rfl

def raw38961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38961Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38961 raw38961Labels = mixedMoment B node2308 node2308Labels := by
  calc
    mixedMoment B raw38961 raw38961Labels = mixedMoment B raw38961step0 raw38961step0Labels := by
      have ha : raw38961step0 = raw38961 := by apply Matrix.ext; unfold raw38961step0 raw38961; decide +kernel
      have hl : raw38961Labels = labelEmbedding2 ∘ raw38961step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38961 raw38961Labels raw38961step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2308 node2308Labels := by rfl

def raw38962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38962Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38962step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38962step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38962step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38962 raw38962Labels = mixedMoment B node3321 node3321Labels := by
  calc
    mixedMoment B raw38962 raw38962Labels = mixedMoment B raw38962step0 raw38962step0Labels := by
      have ha : raw38962step0 = (fun i j => raw38962 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38962step0 raw38962; decide +kernel
      have hl : raw38962step0Labels = raw38962Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38962 raw38962Labels permutation170 permutation7
    mixedMoment B raw38962step0 raw38962step0Labels = mixedMoment B raw38962step1 raw38962step1Labels := by
      have ha : raw38962step1 = -raw38962step0 := by apply Matrix.ext; change ∀ i j, raw38962step1 i j = -(raw38962step0 i j); unfold raw38962step1 raw38962step0; decide +kernel
      have hl : raw38962step1Labels = raw38962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38962step1 raw38962step1Labels = mixedMoment B raw38962step2 raw38962step2Labels := by
      have ha : raw38962step2 = raw38962step1 := by apply Matrix.ext; unfold raw38962step2 raw38962step1; decide +kernel
      have hl : raw38962step1Labels = labelEmbedding4 ∘ raw38962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38962step1 raw38962step1Labels raw38962step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3321 node3321Labels := by rfl

def raw38963 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38963Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38963 raw38963Labels = mixedMoment B node2310 node2310Labels := by
  calc
    mixedMoment B raw38963 raw38963Labels = mixedMoment B raw38963step0 raw38963step0Labels := by
      have ha : raw38963step0 = raw38963 := by apply Matrix.ext; unfold raw38963step0 raw38963; decide +kernel
      have hl : raw38963Labels = labelEmbedding2 ∘ raw38963step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38963 raw38963Labels raw38963step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2310 node2310Labels := by rfl

def raw38964 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38964Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw38964step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38964step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38964 raw38964Labels = mixedMoment B node3329 node3329Labels := by
  calc
    mixedMoment B raw38964 raw38964Labels = mixedMoment B raw38964step0 raw38964step0Labels := by
      have ha : raw38964step0 = (fun i j => raw38964 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38964step0 raw38964; decide +kernel
      have hl : raw38964step0Labels = raw38964Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38964 raw38964Labels permutation33 permutation7
    mixedMoment B raw38964step0 raw38964step0Labels = mixedMoment B raw38964step1 raw38964step1Labels := by
      have ha : raw38964step1 = -raw38964step0 := by apply Matrix.ext; change ∀ i j, raw38964step1 i j = -(raw38964step0 i j); unfold raw38964step1 raw38964step0; decide +kernel
      have hl : raw38964step1Labels = raw38964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38964step1 raw38964step1Labels = mixedMoment B raw38964step2 raw38964step2Labels := by
      have ha : raw38964step2 = raw38964step1 := by apply Matrix.ext; unfold raw38964step2 raw38964step1; decide +kernel
      have hl : raw38964step1Labels = labelEmbedding4 ∘ raw38964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38964step1 raw38964step1Labels raw38964step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3329 node3329Labels := by rfl

def raw38965 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38965Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38965 raw38965Labels = mixedMoment B node2311 node2311Labels := by
  calc
    mixedMoment B raw38965 raw38965Labels = mixedMoment B raw38965step0 raw38965step0Labels := by
      have ha : raw38965step0 = raw38965 := by apply Matrix.ext; unfold raw38965step0 raw38965; decide +kernel
      have hl : raw38965Labels = labelEmbedding2 ∘ raw38965step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38965 raw38965Labels raw38965step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2311 node2311Labels := by rfl

def raw38966 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38966Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw38966step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw38966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38966 raw38966Labels = mixedMoment B node2447 node2447Labels := by
  calc
    mixedMoment B raw38966 raw38966Labels = mixedMoment B raw38966step0 raw38966step0Labels := by
      have ha : raw38966step0 = (fun i j => raw38966 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38966step0 raw38966; decide +kernel
      have hl : raw38966step0Labels = raw38966Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38966 raw38966Labels permutation145 permutation7
    mixedMoment B raw38966step0 raw38966step0Labels = mixedMoment B raw38966step1 raw38966step1Labels := by
      have ha : raw38966step1 = raw38966step0 := by apply Matrix.ext; unfold raw38966step1 raw38966step0; decide +kernel
      have hl : raw38966step0Labels = labelEmbedding4 ∘ raw38966step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38966step0 raw38966step0Labels raw38966step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2447 node2447Labels := by rfl

def raw38967 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38967Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38967 raw38967Labels = mixedMoment B node2313 node2313Labels := by
  calc
    mixedMoment B raw38967 raw38967Labels = mixedMoment B raw38967step0 raw38967step0Labels := by
      have ha : raw38967step0 = raw38967 := by apply Matrix.ext; unfold raw38967step0 raw38967; decide +kernel
      have hl : raw38967Labels = labelEmbedding2 ∘ raw38967step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38967 raw38967Labels raw38967step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2313 node2313Labels := by rfl

def raw38968 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38968Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw38968step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38968step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38968 raw38968Labels = mixedMoment B node3322 node3322Labels := by
  calc
    mixedMoment B raw38968 raw38968Labels = mixedMoment B raw38968step0 raw38968step0Labels := by
      have ha : raw38968step0 = (fun i j => raw38968 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38968step0 raw38968; decide +kernel
      have hl : raw38968step0Labels = raw38968Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38968 raw38968Labels permutation34 permutation7
    mixedMoment B raw38968step0 raw38968step0Labels = mixedMoment B raw38968step1 raw38968step1Labels := by
      have ha : raw38968step1 = -raw38968step0 := by apply Matrix.ext; change ∀ i j, raw38968step1 i j = -(raw38968step0 i j); unfold raw38968step1 raw38968step0; decide +kernel
      have hl : raw38968step1Labels = raw38968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38968step1 raw38968step1Labels = mixedMoment B raw38968step2 raw38968step2Labels := by
      have ha : raw38968step2 = raw38968step1 := by apply Matrix.ext; unfold raw38968step2 raw38968step1; decide +kernel
      have hl : raw38968step1Labels = labelEmbedding4 ∘ raw38968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38968step1 raw38968step1Labels raw38968step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3322 node3322Labels := by rfl

def raw38969 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38969Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38969 raw38969Labels = mixedMoment B node2314 node2314Labels := by
  calc
    mixedMoment B raw38969 raw38969Labels = mixedMoment B raw38969step0 raw38969step0Labels := by
      have ha : raw38969step0 = raw38969 := by apply Matrix.ext; unfold raw38969step0 raw38969; decide +kernel
      have hl : raw38969Labels = labelEmbedding2 ∘ raw38969step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38969 raw38969Labels raw38969step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2314 node2314Labels := by rfl

def raw38970 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38970Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw38970step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38970step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38970 raw38970Labels = mixedMoment B node3330 node3330Labels := by
  calc
    mixedMoment B raw38970 raw38970Labels = mixedMoment B raw38970step0 raw38970step0Labels := by
      have ha : raw38970step0 = (fun i j => raw38970 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38970step0 raw38970; decide +kernel
      have hl : raw38970step0Labels = raw38970Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38970 raw38970Labels permutation35 permutation7
    mixedMoment B raw38970step0 raw38970step0Labels = mixedMoment B raw38970step1 raw38970step1Labels := by
      have ha : raw38970step1 = -raw38970step0 := by apply Matrix.ext; change ∀ i j, raw38970step1 i j = -(raw38970step0 i j); unfold raw38970step1 raw38970step0; decide +kernel
      have hl : raw38970step1Labels = raw38970step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38970step1 raw38970step1Labels = mixedMoment B raw38970step2 raw38970step2Labels := by
      have ha : raw38970step2 = raw38970step1 := by apply Matrix.ext; unfold raw38970step2 raw38970step1; decide +kernel
      have hl : raw38970step1Labels = labelEmbedding4 ∘ raw38970step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38970step1 raw38970step1Labels raw38970step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3330 node3330Labels := by rfl

def raw38971 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw38971Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw38971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38971 raw38971Labels = mixedMoment B node2315 node2315Labels := by
  calc
    mixedMoment B raw38971 raw38971Labels = mixedMoment B raw38971step0 raw38971step0Labels := by
      have ha : raw38971step0 = raw38971 := by apply Matrix.ext; unfold raw38971step0 raw38971; decide +kernel
      have hl : raw38971Labels = labelEmbedding2 ∘ raw38971step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38971 raw38971Labels raw38971step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2315 node2315Labels := by rfl

def raw38972 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw38972Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38972step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![2, 0, -2], ![2, 1, -3]]
def raw38972step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![2, 0, -2], ![2, 1, -3]]
def raw38972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38972 raw38972Labels = mixedMoment B node2369 node2369Labels := by
  calc
    mixedMoment B raw38972 raw38972Labels = mixedMoment B raw38972step0 raw38972step0Labels := by
      have ha : raw38972step0 = (fun i j => raw38972 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38972step0 raw38972; decide +kernel
      have hl : raw38972step0Labels = raw38972Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38972 raw38972Labels permutation25 permutation7
    mixedMoment B raw38972step0 raw38972step0Labels = mixedMoment B raw38972step1 raw38972step1Labels := by
      have ha : raw38972step1 = raw38972step0 := by apply Matrix.ext; unfold raw38972step1 raw38972step0; decide +kernel
      have hl : raw38972step0Labels = labelEmbedding4 ∘ raw38972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38972step0 raw38972step0Labels raw38972step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2369 node2369Labels := by rfl

def raw38973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38973Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38973 raw38973Labels = mixedMoment B node2316 node2316Labels := by
  calc
    mixedMoment B raw38973 raw38973Labels = mixedMoment B raw38973step0 raw38973step0Labels := by
      have ha : raw38973step0 = raw38973 := by apply Matrix.ext; unfold raw38973step0 raw38973; decide +kernel
      have hl : raw38973Labels = labelEmbedding2 ∘ raw38973step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38973 raw38973Labels raw38973step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2316 node2316Labels := by rfl

def raw38974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38974Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw38974step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38974step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38974step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38974 raw38974Labels = mixedMoment B node3398 node3398Labels := by
  calc
    mixedMoment B raw38974 raw38974Labels = mixedMoment B raw38974step0 raw38974step0Labels := by
      have ha : raw38974step0 = (fun i j => raw38974 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38974step0 raw38974; decide +kernel
      have hl : raw38974step0Labels = raw38974Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38974 raw38974Labels permutation152 permutation7
    mixedMoment B raw38974step0 raw38974step0Labels = mixedMoment B raw38974step1 raw38974step1Labels := by
      have ha : raw38974step1 = -raw38974step0 := by apply Matrix.ext; change ∀ i j, raw38974step1 i j = -(raw38974step0 i j); unfold raw38974step1 raw38974step0; decide +kernel
      have hl : raw38974step1Labels = raw38974step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38974step1 raw38974step1Labels = mixedMoment B raw38974step2 raw38974step2Labels := by
      have ha : raw38974step2 = raw38974step1 := by apply Matrix.ext; unfold raw38974step2 raw38974step1; decide +kernel
      have hl : raw38974step1Labels = labelEmbedding4 ∘ raw38974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38974step1 raw38974step1Labels raw38974step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3398 node3398Labels := by rfl

def raw38975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38975Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38975 raw38975Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw38975 raw38975Labels = mixedMoment B raw38975step0 raw38975step0Labels := by
      have ha : raw38975step0 = raw38975 := by apply Matrix.ext; unfold raw38975step0 raw38975; decide +kernel
      have hl : raw38975Labels = labelEmbedding2 ∘ raw38975step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38975 raw38975Labels raw38975step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2317 node2317Labels := by rfl

def raw38976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38976Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38976step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38976step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38976step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38976 raw38976Labels = mixedMoment B node3399 node3399Labels := by
  calc
    mixedMoment B raw38976 raw38976Labels = mixedMoment B raw38976step0 raw38976step0Labels := by
      have ha : raw38976step0 = (fun i j => raw38976 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38976step0 raw38976; decide +kernel
      have hl : raw38976step0Labels = raw38976Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38976 raw38976Labels permutation152 permutation7
    mixedMoment B raw38976step0 raw38976step0Labels = mixedMoment B raw38976step1 raw38976step1Labels := by
      have ha : raw38976step1 = -raw38976step0 := by apply Matrix.ext; change ∀ i j, raw38976step1 i j = -(raw38976step0 i j); unfold raw38976step1 raw38976step0; decide +kernel
      have hl : raw38976step1Labels = raw38976step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38976step1 raw38976step1Labels = mixedMoment B raw38976step2 raw38976step2Labels := by
      have ha : raw38976step2 = raw38976step1 := by apply Matrix.ext; unfold raw38976step2 raw38976step1; decide +kernel
      have hl : raw38976step1Labels = labelEmbedding4 ∘ raw38976step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38976step1 raw38976step1Labels raw38976step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3399 node3399Labels := by rfl

def raw38977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38977Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38977 raw38977Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw38977 raw38977Labels = mixedMoment B raw38977step0 raw38977step0Labels := by
      have ha : raw38977step0 = raw38977 := by apply Matrix.ext; unfold raw38977step0 raw38977; decide +kernel
      have hl : raw38977Labels = labelEmbedding2 ∘ raw38977step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38977 raw38977Labels raw38977step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2318 node2318Labels := by rfl

def raw38978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38978Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38978step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38978step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38978step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38978 raw38978Labels = mixedMoment B node3400 node3400Labels := by
  calc
    mixedMoment B raw38978 raw38978Labels = mixedMoment B raw38978step0 raw38978step0Labels := by
      have ha : raw38978step0 = (fun i j => raw38978 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38978step0 raw38978; decide +kernel
      have hl : raw38978step0Labels = raw38978Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38978 raw38978Labels permutation152 permutation7
    mixedMoment B raw38978step0 raw38978step0Labels = mixedMoment B raw38978step1 raw38978step1Labels := by
      have ha : raw38978step1 = -raw38978step0 := by apply Matrix.ext; change ∀ i j, raw38978step1 i j = -(raw38978step0 i j); unfold raw38978step1 raw38978step0; decide +kernel
      have hl : raw38978step1Labels = raw38978step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38978step1 raw38978step1Labels = mixedMoment B raw38978step2 raw38978step2Labels := by
      have ha : raw38978step2 = raw38978step1 := by apply Matrix.ext; unfold raw38978step2 raw38978step1; decide +kernel
      have hl : raw38978step1Labels = labelEmbedding4 ∘ raw38978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38978step1 raw38978step1Labels raw38978step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3400 node3400Labels := by rfl

def raw38979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38979Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38979 raw38979Labels = mixedMoment B node2328 node2328Labels := by
  calc
    mixedMoment B raw38979 raw38979Labels = mixedMoment B raw38979step0 raw38979step0Labels := by
      have ha : raw38979step0 = raw38979 := by apply Matrix.ext; unfold raw38979step0 raw38979; decide +kernel
      have hl : raw38979Labels = labelEmbedding2 ∘ raw38979step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38979 raw38979Labels raw38979step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2328 node2328Labels := by rfl

def raw38980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38980Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38980step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38980step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38980step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38980 raw38980Labels = mixedMoment B node3401 node3401Labels := by
  calc
    mixedMoment B raw38980 raw38980Labels = mixedMoment B raw38980step0 raw38980step0Labels := by
      have ha : raw38980step0 = (fun i j => raw38980 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38980step0 raw38980; decide +kernel
      have hl : raw38980step0Labels = raw38980Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38980 raw38980Labels permutation152 permutation7
    mixedMoment B raw38980step0 raw38980step0Labels = mixedMoment B raw38980step1 raw38980step1Labels := by
      have ha : raw38980step1 = -raw38980step0 := by apply Matrix.ext; change ∀ i j, raw38980step1 i j = -(raw38980step0 i j); unfold raw38980step1 raw38980step0; decide +kernel
      have hl : raw38980step1Labels = raw38980step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38980step1 raw38980step1Labels = mixedMoment B raw38980step2 raw38980step2Labels := by
      have ha : raw38980step2 = raw38980step1 := by apply Matrix.ext; unfold raw38980step2 raw38980step1; decide +kernel
      have hl : raw38980step1Labels = labelEmbedding4 ∘ raw38980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38980step1 raw38980step1Labels raw38980step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3401 node3401Labels := by rfl

def raw38981 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38981Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38981 raw38981Labels = mixedMoment B node2329 node2329Labels := by
  calc
    mixedMoment B raw38981 raw38981Labels = mixedMoment B raw38981step0 raw38981step0Labels := by
      have ha : raw38981step0 = raw38981 := by apply Matrix.ext; unfold raw38981step0 raw38981; decide +kernel
      have hl : raw38981Labels = labelEmbedding2 ∘ raw38981step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38981 raw38981Labels raw38981step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2329 node2329Labels := by rfl

def raw38982 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38982Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw38982step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38982step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38982 raw38982Labels = mixedMoment B node3402 node3402Labels := by
  calc
    mixedMoment B raw38982 raw38982Labels = mixedMoment B raw38982step0 raw38982step0Labels := by
      have ha : raw38982step0 = (fun i j => raw38982 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38982step0 raw38982; decide +kernel
      have hl : raw38982step0Labels = raw38982Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38982 raw38982Labels permutation32 permutation7
    mixedMoment B raw38982step0 raw38982step0Labels = mixedMoment B raw38982step1 raw38982step1Labels := by
      have ha : raw38982step1 = -raw38982step0 := by apply Matrix.ext; change ∀ i j, raw38982step1 i j = -(raw38982step0 i j); unfold raw38982step1 raw38982step0; decide +kernel
      have hl : raw38982step1Labels = raw38982step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38982step1 raw38982step1Labels = mixedMoment B raw38982step2 raw38982step2Labels := by
      have ha : raw38982step2 = raw38982step1 := by apply Matrix.ext; unfold raw38982step2 raw38982step1; decide +kernel
      have hl : raw38982step1Labels = labelEmbedding4 ∘ raw38982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38982step1 raw38982step1Labels raw38982step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3402 node3402Labels := by rfl

def raw38983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38983Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38983 raw38983Labels = mixedMoment B node2330 node2330Labels := by
  calc
    mixedMoment B raw38983 raw38983Labels = mixedMoment B raw38983step0 raw38983step0Labels := by
      have ha : raw38983step0 = raw38983 := by apply Matrix.ext; unfold raw38983step0 raw38983; decide +kernel
      have hl : raw38983Labels = labelEmbedding2 ∘ raw38983step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38983 raw38983Labels raw38983step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2330 node2330Labels := by rfl

def raw38984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38984Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38984step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38984step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38984step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38984 raw38984Labels = mixedMoment B node3404 node3404Labels := by
  calc
    mixedMoment B raw38984 raw38984Labels = mixedMoment B raw38984step0 raw38984step0Labels := by
      have ha : raw38984step0 = (fun i j => raw38984 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38984step0 raw38984; decide +kernel
      have hl : raw38984step0Labels = raw38984Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38984 raw38984Labels permutation152 permutation7
    mixedMoment B raw38984step0 raw38984step0Labels = mixedMoment B raw38984step1 raw38984step1Labels := by
      have ha : raw38984step1 = -raw38984step0 := by apply Matrix.ext; change ∀ i j, raw38984step1 i j = -(raw38984step0 i j); unfold raw38984step1 raw38984step0; decide +kernel
      have hl : raw38984step1Labels = raw38984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38984step1 raw38984step1Labels = mixedMoment B raw38984step2 raw38984step2Labels := by
      have ha : raw38984step2 = raw38984step1 := by apply Matrix.ext; unfold raw38984step2 raw38984step1; decide +kernel
      have hl : raw38984step1Labels = labelEmbedding4 ∘ raw38984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38984step1 raw38984step1Labels raw38984step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3404 node3404Labels := by rfl

def raw38985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38985Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38985 raw38985Labels = mixedMoment B node2332 node2332Labels := by
  calc
    mixedMoment B raw38985 raw38985Labels = mixedMoment B raw38985step0 raw38985step0Labels := by
      have ha : raw38985step0 = raw38985 := by apply Matrix.ext; unfold raw38985step0 raw38985; decide +kernel
      have hl : raw38985Labels = labelEmbedding2 ∘ raw38985step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38985 raw38985Labels raw38985step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2332 node2332Labels := by rfl

def raw38986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38986Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38986step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38986step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38986step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38986 raw38986Labels = mixedMoment B node3410 node3410Labels := by
  calc
    mixedMoment B raw38986 raw38986Labels = mixedMoment B raw38986step0 raw38986step0Labels := by
      have ha : raw38986step0 = (fun i j => raw38986 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38986step0 raw38986; decide +kernel
      have hl : raw38986step0Labels = raw38986Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38986 raw38986Labels permutation152 permutation7
    mixedMoment B raw38986step0 raw38986step0Labels = mixedMoment B raw38986step1 raw38986step1Labels := by
      have ha : raw38986step1 = -raw38986step0 := by apply Matrix.ext; change ∀ i j, raw38986step1 i j = -(raw38986step0 i j); unfold raw38986step1 raw38986step0; decide +kernel
      have hl : raw38986step1Labels = raw38986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38986step1 raw38986step1Labels = mixedMoment B raw38986step2 raw38986step2Labels := by
      have ha : raw38986step2 = raw38986step1 := by apply Matrix.ext; unfold raw38986step2 raw38986step1; decide +kernel
      have hl : raw38986step1Labels = labelEmbedding4 ∘ raw38986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38986step1 raw38986step1Labels raw38986step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3410 node3410Labels := by rfl

def raw38987 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38987Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38987 raw38987Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw38987 raw38987Labels = mixedMoment B raw38987step0 raw38987step0Labels := by
      have ha : raw38987step0 = raw38987 := by apply Matrix.ext; unfold raw38987step0 raw38987; decide +kernel
      have hl : raw38987Labels = labelEmbedding2 ∘ raw38987step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38987 raw38987Labels raw38987step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw38988 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38988Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38988step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38988step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38988 raw38988Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw38988 raw38988Labels = mixedMoment B raw38988step0 raw38988step0Labels := by
      have ha : raw38988step0 = (fun i j => raw38988 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38988step0 raw38988; decide +kernel
      have hl : raw38988step0Labels = raw38988Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38988 raw38988Labels permutation32 permutation7
    mixedMoment B raw38988step0 raw38988step0Labels = mixedMoment B raw38988step1 raw38988step1Labels := by
      have ha : raw38988step1 = -raw38988step0 := by apply Matrix.ext; change ∀ i j, raw38988step1 i j = -(raw38988step0 i j); unfold raw38988step1 raw38988step0; decide +kernel
      have hl : raw38988step1Labels = raw38988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38988step1 raw38988step1Labels = mixedMoment B raw38988step2 raw38988step2Labels := by
      have ha : raw38988step2 = raw38988step1 := by apply Matrix.ext; unfold raw38988step2 raw38988step1; decide +kernel
      have hl : raw38988step1Labels = labelEmbedding4 ∘ raw38988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38988step1 raw38988step1Labels raw38988step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

def raw38989 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38989Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38989 raw38989Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw38989 raw38989Labels = mixedMoment B raw38989step0 raw38989step0Labels := by
      have ha : raw38989step0 = raw38989 := by apply Matrix.ext; unfold raw38989step0 raw38989; decide +kernel
      have hl : raw38989Labels = labelEmbedding2 ∘ raw38989step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38989 raw38989Labels raw38989step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2337 node2337Labels := by rfl

def raw38990 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38990Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38990step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38990step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38990 raw38990Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw38990 raw38990Labels = mixedMoment B raw38990step0 raw38990step0Labels := by
      have ha : raw38990step0 = (fun i j => raw38990 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38990step0 raw38990; decide +kernel
      have hl : raw38990step0Labels = raw38990Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38990 raw38990Labels permutation32 permutation7
    mixedMoment B raw38990step0 raw38990step0Labels = mixedMoment B raw38990step1 raw38990step1Labels := by
      have ha : raw38990step1 = -raw38990step0 := by apply Matrix.ext; change ∀ i j, raw38990step1 i j = -(raw38990step0 i j); unfold raw38990step1 raw38990step0; decide +kernel
      have hl : raw38990step1Labels = raw38990step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38990step1 raw38990step1Labels = mixedMoment B raw38990step2 raw38990step2Labels := by
      have ha : raw38990step2 = raw38990step1 := by apply Matrix.ext; unfold raw38990step2 raw38990step1; decide +kernel
      have hl : raw38990step1Labels = labelEmbedding4 ∘ raw38990step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38990step1 raw38990step1Labels raw38990step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

def raw38991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38991Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38991step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38991 raw38991Labels = mixedMoment B node2338 node2338Labels := by
  calc
    mixedMoment B raw38991 raw38991Labels = mixedMoment B raw38991step0 raw38991step0Labels := by
      have ha : raw38991step0 = raw38991 := by apply Matrix.ext; unfold raw38991step0 raw38991; decide +kernel
      have hl : raw38991Labels = labelEmbedding2 ∘ raw38991step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38991 raw38991Labels raw38991step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2338 node2338Labels := by rfl

def raw38992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38992Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38992step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38992step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38992step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38992 raw38992Labels = mixedMoment B node3416 node3416Labels := by
  calc
    mixedMoment B raw38992 raw38992Labels = mixedMoment B raw38992step0 raw38992step0Labels := by
      have ha : raw38992step0 = (fun i j => raw38992 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38992step0 raw38992; decide +kernel
      have hl : raw38992step0Labels = raw38992Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38992 raw38992Labels permutation170 permutation7
    mixedMoment B raw38992step0 raw38992step0Labels = mixedMoment B raw38992step1 raw38992step1Labels := by
      have ha : raw38992step1 = -raw38992step0 := by apply Matrix.ext; change ∀ i j, raw38992step1 i j = -(raw38992step0 i j); unfold raw38992step1 raw38992step0; decide +kernel
      have hl : raw38992step1Labels = raw38992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38992step1 raw38992step1Labels = mixedMoment B raw38992step2 raw38992step2Labels := by
      have ha : raw38992step2 = raw38992step1 := by apply Matrix.ext; unfold raw38992step2 raw38992step1; decide +kernel
      have hl : raw38992step1Labels = labelEmbedding4 ∘ raw38992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38992step1 raw38992step1Labels raw38992step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3416 node3416Labels := by rfl

def raw38993 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38993Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38993 raw38993Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw38993 raw38993Labels = mixedMoment B raw38993step0 raw38993step0Labels := by
      have ha : raw38993step0 = raw38993 := by apply Matrix.ext; unfold raw38993step0 raw38993; decide +kernel
      have hl : raw38993Labels = labelEmbedding2 ∘ raw38993step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38993 raw38993Labels raw38993step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2339 node2339Labels := by rfl

def raw38994 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38994Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38994step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38994step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38994 raw38994Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw38994 raw38994Labels = mixedMoment B raw38994step0 raw38994step0Labels := by
      have ha : raw38994step0 = (fun i j => raw38994 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38994step0 raw38994; decide +kernel
      have hl : raw38994step0Labels = raw38994Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38994 raw38994Labels permutation32 permutation7
    mixedMoment B raw38994step0 raw38994step0Labels = mixedMoment B raw38994step1 raw38994step1Labels := by
      have ha : raw38994step1 = -raw38994step0 := by apply Matrix.ext; change ∀ i j, raw38994step1 i j = -(raw38994step0 i j); unfold raw38994step1 raw38994step0; decide +kernel
      have hl : raw38994step1Labels = raw38994step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38994step1 raw38994step1Labels = mixedMoment B raw38994step2 raw38994step2Labels := by
      have ha : raw38994step2 = raw38994step1 := by apply Matrix.ext; unfold raw38994step2 raw38994step1; decide +kernel
      have hl : raw38994step1Labels = labelEmbedding4 ∘ raw38994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38994step1 raw38994step1Labels raw38994step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3420 node3420Labels := by rfl

def raw38995 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38995Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38995 raw38995Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw38995 raw38995Labels = mixedMoment B raw38995step0 raw38995step0Labels := by
      have ha : raw38995step0 = raw38995 := by apply Matrix.ext; unfold raw38995step0 raw38995; decide +kernel
      have hl : raw38995Labels = labelEmbedding2 ∘ raw38995step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38995 raw38995Labels raw38995step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw38996 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38996Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw38996step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38996step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38996 raw38996Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw38996 raw38996Labels = mixedMoment B raw38996step0 raw38996step0Labels := by
      have ha : raw38996step0 = (fun i j => raw38996 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38996step0 raw38996; decide +kernel
      have hl : raw38996step0Labels = raw38996Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38996 raw38996Labels permutation34 permutation7
    mixedMoment B raw38996step0 raw38996step0Labels = mixedMoment B raw38996step1 raw38996step1Labels := by
      have ha : raw38996step1 = -raw38996step0 := by apply Matrix.ext; change ∀ i j, raw38996step1 i j = -(raw38996step0 i j); unfold raw38996step1 raw38996step0; decide +kernel
      have hl : raw38996step1Labels = raw38996step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38996step1 raw38996step1Labels = mixedMoment B raw38996step2 raw38996step2Labels := by
      have ha : raw38996step2 = raw38996step1 := by apply Matrix.ext; unfold raw38996step2 raw38996step1; decide +kernel
      have hl : raw38996step1Labels = labelEmbedding4 ∘ raw38996step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38996step1 raw38996step1Labels raw38996step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3417 node3417Labels := by rfl

def raw38997 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38997Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38997 raw38997Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw38997 raw38997Labels = mixedMoment B raw38997step0 raw38997step0Labels := by
      have ha : raw38997step0 = raw38997 := by apply Matrix.ext; unfold raw38997step0 raw38997; decide +kernel
      have hl : raw38997Labels = labelEmbedding2 ∘ raw38997step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38997 raw38997Labels raw38997step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw38998 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38998Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38998step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38998step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38998 raw38998Labels = mixedMoment B node3421 node3421Labels := by
  calc
    mixedMoment B raw38998 raw38998Labels = mixedMoment B raw38998step0 raw38998step0Labels := by
      have ha : raw38998step0 = (fun i j => raw38998 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38998step0 raw38998; decide +kernel
      have hl : raw38998step0Labels = raw38998Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38998 raw38998Labels permutation32 permutation7
    mixedMoment B raw38998step0 raw38998step0Labels = mixedMoment B raw38998step1 raw38998step1Labels := by
      have ha : raw38998step1 = -raw38998step0 := by apply Matrix.ext; change ∀ i j, raw38998step1 i j = -(raw38998step0 i j); unfold raw38998step1 raw38998step0; decide +kernel
      have hl : raw38998step1Labels = raw38998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38998step1 raw38998step1Labels = mixedMoment B raw38998step2 raw38998step2Labels := by
      have ha : raw38998step2 = raw38998step1 := by apply Matrix.ext; unfold raw38998step2 raw38998step1; decide +kernel
      have hl : raw38998step1Labels = labelEmbedding4 ∘ raw38998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38998step1 raw38998step1Labels raw38998step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3421 node3421Labels := by rfl

def raw38999 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw38999Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38999step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw38999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38999 raw38999Labels = mixedMoment B node2344 node2344Labels := by
  calc
    mixedMoment B raw38999 raw38999Labels = mixedMoment B raw38999step0 raw38999step0Labels := by
      have ha : raw38999step0 = raw38999 := by apply Matrix.ext; unfold raw38999step0 raw38999; decide +kernel
      have hl : raw38999Labels = labelEmbedding2 ∘ raw38999step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38999 raw38999Labels raw38999step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2344 node2344Labels := by rfl

def raw39000 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw39000Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39000step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw39000step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw39000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39000 raw39000Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw39000 raw39000Labels = mixedMoment B raw39000step0 raw39000step0Labels := by
      have ha : raw39000step0 = (fun i j => raw39000 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39000step0 raw39000; decide +kernel
      have hl : raw39000step0Labels = raw39000Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39000 raw39000Labels permutation31 permutation7
    mixedMoment B raw39000step0 raw39000step0Labels = mixedMoment B raw39000step1 raw39000step1Labels := by
      have ha : raw39000step1 = raw39000step0 := by apply Matrix.ext; unfold raw39000step1 raw39000step0; decide +kernel
      have hl : raw39000step0Labels = labelEmbedding4 ∘ raw39000step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39000step0 raw39000step0Labels raw39000step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3422 node3422Labels := by rfl

def raw39001 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw39001Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39001step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw39001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39001 raw39001Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw39001 raw39001Labels = mixedMoment B raw39001step0 raw39001step0Labels := by
      have ha : raw39001step0 = raw39001 := by apply Matrix.ext; unfold raw39001step0 raw39001; decide +kernel
      have hl : raw39001Labels = labelEmbedding2 ∘ raw39001step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39001 raw39001Labels raw39001step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2345 node2345Labels := by rfl

def raw39002 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw39002Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39002step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw39002step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw39002step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw39002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39002 raw39002Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw39002 raw39002Labels = mixedMoment B raw39002step0 raw39002step0Labels := by
      have ha : raw39002step0 = (fun i j => raw39002 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39002step0 raw39002; decide +kernel
      have hl : raw39002step0Labels = raw39002Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39002 raw39002Labels permutation9 permutation7
    mixedMoment B raw39002step0 raw39002step0Labels = mixedMoment B raw39002step1 raw39002step1Labels := by
      have ha : raw39002step1 = -raw39002step0 := by apply Matrix.ext; change ∀ i j, raw39002step1 i j = -(raw39002step0 i j); unfold raw39002step1 raw39002step0; decide +kernel
      have hl : raw39002step1Labels = raw39002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39002step1 raw39002step1Labels = mixedMoment B raw39002step2 raw39002step2Labels := by
      have ha : raw39002step2 = raw39002step1 := by apply Matrix.ext; unfold raw39002step2 raw39002step1; decide +kernel
      have hl : raw39002step1Labels = labelEmbedding4 ∘ raw39002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39002step1 raw39002step1Labels raw39002step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

def raw39003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw39003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw39003step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw39003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39003 raw39003Labels = mixedMoment B node3426 node3426Labels := by
  calc
    mixedMoment B raw39003 raw39003Labels = mixedMoment B raw39003step0 raw39003step0Labels := by
      have ha : raw39003step0 = (fun i j => raw39003 (permutation663 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39003step0 raw39003; decide +kernel
      have hl : raw39003step0Labels = raw39003Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39003 raw39003Labels permutation663 permutation5
    mixedMoment B raw39003step0 raw39003step0Labels = mixedMoment B raw39003step1 raw39003step1Labels := by
      have ha : raw39003step1 = raw39003step0 := by apply Matrix.ext; unfold raw39003step1 raw39003step0; decide +kernel
      have hl : raw39003step0Labels = labelEmbedding1 ∘ raw39003step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39003step0 raw39003step0Labels raw39003step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3426 node3426Labels := by rfl

def raw39004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw39004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw39004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw39004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39004step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw39004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39004 raw39004Labels = mixedMoment B node3589 node3589Labels := by
  calc
    mixedMoment B raw39004 raw39004Labels = mixedMoment B raw39004step0 raw39004step0Labels := by
      have ha : raw39004step0 = (fun i j => raw39004 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39004step0 raw39004; decide +kernel
      have hl : raw39004step0Labels = raw39004Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39004 raw39004Labels permutation160 permutation7
    mixedMoment B raw39004step0 raw39004step0Labels = mixedMoment B raw39004step1 raw39004step1Labels := by
      have ha : raw39004step1 = -raw39004step0 := by apply Matrix.ext; change ∀ i j, raw39004step1 i j = -(raw39004step0 i j); unfold raw39004step1 raw39004step0; decide +kernel
      have hl : raw39004step1Labels = raw39004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39004step1 raw39004step1Labels = mixedMoment B raw39004step2 raw39004step2Labels := by
      have ha : raw39004step2 = raw39004step1 := by apply Matrix.ext; unfold raw39004step2 raw39004step1; decide +kernel
      have hl : raw39004step1Labels = labelEmbedding1 ∘ raw39004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39004step1 raw39004step1Labels raw39004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3589 node3589Labels := by rfl

def raw39005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw39005Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw39005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39005 raw39005Labels = mixedMoment B node2795 node2795Labels := by
  calc
    mixedMoment B raw39005 raw39005Labels = mixedMoment B raw39005step0 raw39005step0Labels := by
      have ha : raw39005step0 = (fun i j => raw39005 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39005step0 raw39005; decide +kernel
      have hl : raw39005step0Labels = raw39005Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39005 raw39005Labels permutation152 permutation3
    _ = mixedMoment B node2795 node2795Labels := by rfl

def raw39006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw39006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw39006step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw39006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39006step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw39006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39006 raw39006Labels = mixedMoment B node3593 node3593Labels := by
  calc
    mixedMoment B raw39006 raw39006Labels = mixedMoment B raw39006step0 raw39006step0Labels := by
      have ha : raw39006step0 = (fun i j => raw39006 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39006step0 raw39006; decide +kernel
      have hl : raw39006step0Labels = raw39006Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39006 raw39006Labels permutation168 permutation7
    mixedMoment B raw39006step0 raw39006step0Labels = mixedMoment B raw39006step1 raw39006step1Labels := by
      have ha : raw39006step1 = -raw39006step0 := by apply Matrix.ext; change ∀ i j, raw39006step1 i j = -(raw39006step0 i j); unfold raw39006step1 raw39006step0; decide +kernel
      have hl : raw39006step1Labels = raw39006step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39006step1 raw39006step1Labels = mixedMoment B raw39006step2 raw39006step2Labels := by
      have ha : raw39006step2 = raw39006step1 := by apply Matrix.ext; unfold raw39006step2 raw39006step1; decide +kernel
      have hl : raw39006step1Labels = labelEmbedding1 ∘ raw39006step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39006step1 raw39006step1Labels raw39006step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3593 node3593Labels := by rfl

def raw39007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw39007step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw39007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39007step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw39007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39007 raw39007Labels = mixedMoment B node3585 node3585Labels := by
  calc
    mixedMoment B raw39007 raw39007Labels = mixedMoment B raw39007step0 raw39007step0Labels := by
      have ha : raw39007step0 = (fun i j => raw39007 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39007step0 raw39007; decide +kernel
      have hl : raw39007step0Labels = raw39007Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39007 raw39007Labels permutation152 permutation7
    mixedMoment B raw39007step0 raw39007step0Labels = mixedMoment B raw39007step1 raw39007step1Labels := by
      have ha : raw39007step1 = -raw39007step0 := by apply Matrix.ext; change ∀ i j, raw39007step1 i j = -(raw39007step0 i j); unfold raw39007step1 raw39007step0; decide +kernel
      have hl : raw39007step1Labels = raw39007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39007step1 raw39007step1Labels = mixedMoment B raw39007step2 raw39007step2Labels := by
      have ha : raw39007step2 = raw39007step1 := by apply Matrix.ext; unfold raw39007step2 raw39007step1; decide +kernel
      have hl : raw39007step1Labels = labelEmbedding1 ∘ raw39007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39007step1 raw39007step1Labels raw39007step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3585 node3585Labels := by rfl

def raw39008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39008 raw39008Labels = mixedMoment B node3587 node3587Labels := by
  calc
    mixedMoment B raw39008 raw39008Labels = mixedMoment B raw39008step0 raw39008step0Labels := by
      have ha : raw39008step0 = (fun i j => raw39008 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39008step0 raw39008; decide +kernel
      have hl : raw39008step0Labels = raw39008Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39008 raw39008Labels permutation152 permutation7
    mixedMoment B raw39008step0 raw39008step0Labels = mixedMoment B raw39008step1 raw39008step1Labels := by
      have ha : raw39008step1 = -raw39008step0 := by apply Matrix.ext; change ∀ i j, raw39008step1 i j = -(raw39008step0 i j); unfold raw39008step1 raw39008step0; decide +kernel
      have hl : raw39008step1Labels = raw39008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39008step1 raw39008step1Labels = mixedMoment B raw39008step2 raw39008step2Labels := by
      have ha : raw39008step2 = raw39008step1 := by apply Matrix.ext; unfold raw39008step2 raw39008step1; decide +kernel
      have hl : raw39008step1Labels = labelEmbedding1 ∘ raw39008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39008step1 raw39008step1Labels raw39008step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3587 node3587Labels := by rfl

def raw39009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw39009step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39009step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw39009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39009step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw39009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39009 raw39009Labels = mixedMoment B node3586 node3586Labels := by
  calc
    mixedMoment B raw39009 raw39009Labels = mixedMoment B raw39009step0 raw39009step0Labels := by
      have ha : raw39009step0 = (fun i j => raw39009 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39009step0 raw39009; decide +kernel
      have hl : raw39009step0Labels = raw39009Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39009 raw39009Labels permutation153 permutation7
    mixedMoment B raw39009step0 raw39009step0Labels = mixedMoment B raw39009step1 raw39009step1Labels := by
      have ha : raw39009step1 = -raw39009step0 := by apply Matrix.ext; change ∀ i j, raw39009step1 i j = -(raw39009step0 i j); unfold raw39009step1 raw39009step0; decide +kernel
      have hl : raw39009step1Labels = raw39009step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39009step1 raw39009step1Labels = mixedMoment B raw39009step2 raw39009step2Labels := by
      have ha : raw39009step2 = raw39009step1 := by apply Matrix.ext; unfold raw39009step2 raw39009step1; decide +kernel
      have hl : raw39009step1Labels = labelEmbedding1 ∘ raw39009step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39009step1 raw39009step1Labels raw39009step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3586 node3586Labels := by rfl

def raw39010 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw39010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39010 raw39010Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw39010 raw39010Labels = mixedMoment B raw39010step0 raw39010step0Labels := by
      have ha : raw39010step0 = (fun i j => raw39010 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39010step0 raw39010; decide +kernel
      have hl : raw39010step0Labels = raw39010Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39010 raw39010Labels permutation32 permutation3
    _ = mixedMoment B node2815 node2815Labels := by rfl

def raw39011 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw39011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw39011step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw39011step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw39011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39011 raw39011Labels = mixedMoment B node3588 node3588Labels := by
  calc
    mixedMoment B raw39011 raw39011Labels = mixedMoment B raw39011step0 raw39011step0Labels := by
      have ha : raw39011step0 = (fun i j => raw39011 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39011step0 raw39011; decide +kernel
      have hl : raw39011step0Labels = raw39011Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39011 raw39011Labels permutation32 permutation7
    mixedMoment B raw39011step0 raw39011step0Labels = mixedMoment B raw39011step1 raw39011step1Labels := by
      have ha : raw39011step1 = -raw39011step0 := by apply Matrix.ext; change ∀ i j, raw39011step1 i j = -(raw39011step0 i j); unfold raw39011step1 raw39011step0; decide +kernel
      have hl : raw39011step1Labels = raw39011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39011step1 raw39011step1Labels = mixedMoment B raw39011step2 raw39011step2Labels := by
      have ha : raw39011step2 = raw39011step1 := by apply Matrix.ext; unfold raw39011step2 raw39011step1; decide +kernel
      have hl : raw39011step1Labels = labelEmbedding1 ∘ raw39011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39011step1 raw39011step1Labels raw39011step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3588 node3588Labels := by rfl

def raw39012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]
def raw39012step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw39012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39012step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw39012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39012 raw39012Labels = mixedMoment B node3590 node3590Labels := by
  calc
    mixedMoment B raw39012 raw39012Labels = mixedMoment B raw39012step0 raw39012step0Labels := by
      have ha : raw39012step0 = (fun i j => raw39012 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39012step0 raw39012; decide +kernel
      have hl : raw39012step0Labels = raw39012Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39012 raw39012Labels permutation156 permutation7
    mixedMoment B raw39012step0 raw39012step0Labels = mixedMoment B raw39012step1 raw39012step1Labels := by
      have ha : raw39012step1 = -raw39012step0 := by apply Matrix.ext; change ∀ i j, raw39012step1 i j = -(raw39012step0 i j); unfold raw39012step1 raw39012step0; decide +kernel
      have hl : raw39012step1Labels = raw39012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39012step1 raw39012step1Labels = mixedMoment B raw39012step2 raw39012step2Labels := by
      have ha : raw39012step2 = raw39012step1 := by apply Matrix.ext; unfold raw39012step2 raw39012step1; decide +kernel
      have hl : raw39012step1Labels = labelEmbedding1 ∘ raw39012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39012step1 raw39012step1Labels raw39012step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3590 node3590Labels := by rfl

def raw39013 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39013Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw39013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw39013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw39013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39013 raw39013Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw39013 raw39013Labels = mixedMoment B raw39013step0 raw39013step0Labels := by
      have ha : raw39013step0 = (fun i j => raw39013 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39013step0 raw39013; decide +kernel
      have hl : raw39013step0Labels = raw39013Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39013 raw39013Labels permutation145 permutation3
    mixedMoment B raw39013step0 raw39013step0Labels = mixedMoment B raw39013step1 raw39013step1Labels := by
      have ha : raw39013step1 = -raw39013step0 := by apply Matrix.ext; change ∀ i j, raw39013step1 i j = -(raw39013step0 i j); unfold raw39013step1 raw39013step0; decide +kernel
      have hl : raw39013step1Labels = raw39013step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2434 node2434Labels := by rfl

def raw39014 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw39014step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw39014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39014 raw39014Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw39014 raw39014Labels = mixedMoment B raw39014step0 raw39014step0Labels := by
      have ha : raw39014step0 = (fun i j => raw39014 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39014step0 raw39014; decide +kernel
      have hl : raw39014step0Labels = raw39014Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39014 raw39014Labels permutation144 permutation5
    mixedMoment B raw39014step0 raw39014step0Labels = mixedMoment B raw39014step1 raw39014step1Labels := by
      have ha : raw39014step1 = raw39014step0 := by apply Matrix.ext; unfold raw39014step1 raw39014step0; decide +kernel
      have hl : raw39014step0Labels = labelEmbedding1 ∘ raw39014step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39014step0 raw39014step0Labels raw39014step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

def raw39015 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39015Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39015 raw39015Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw39015 raw39015Labels = mixedMoment B raw39015step0 raw39015step0Labels := by
      have ha : raw39015step0 = (fun i j => raw39015 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39015step0 raw39015; decide +kernel
      have hl : raw39015step0Labels = raw39015Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39015 raw39015Labels permutation33 permutation3
    _ = mixedMoment B node2817 node2817Labels := by rfl

def raw39016 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw39016step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw39016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw39016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39016 raw39016Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw39016 raw39016Labels = mixedMoment B raw39016step0 raw39016step0Labels := by
      have ha : raw39016step0 = (fun i j => raw39016 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39016step0 raw39016; decide +kernel
      have hl : raw39016step0Labels = raw39016Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39016 raw39016Labels permutation32 permutation7
    mixedMoment B raw39016step0 raw39016step0Labels = mixedMoment B raw39016step1 raw39016step1Labels := by
      have ha : raw39016step1 = -raw39016step0 := by apply Matrix.ext; change ∀ i j, raw39016step1 i j = -(raw39016step0 i j); unfold raw39016step1 raw39016step0; decide +kernel
      have hl : raw39016step1Labels = raw39016step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39016step1 raw39016step1Labels = mixedMoment B raw39016step2 raw39016step2Labels := by
      have ha : raw39016step2 = raw39016step1 := by apply Matrix.ext; unfold raw39016step2 raw39016step1; decide +kernel
      have hl : raw39016step1Labels = labelEmbedding1 ∘ raw39016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39016step1 raw39016step1Labels raw39016step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3591 node3591Labels := by rfl

def raw39017 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39017Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39017 raw39017Labels = mixedMoment B node2818 node2818Labels := by
  calc
    mixedMoment B raw39017 raw39017Labels = mixedMoment B raw39017step0 raw39017step0Labels := by
      have ha : raw39017step0 = (fun i j => raw39017 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39017step0 raw39017; decide +kernel
      have hl : raw39017step0Labels = raw39017Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39017 raw39017Labels permutation32 permutation3
    _ = mixedMoment B node2818 node2818Labels := by rfl

def raw39018 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39018Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw39018step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw39018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw39018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39018 raw39018Labels = mixedMoment B node3592 node3592Labels := by
  calc
    mixedMoment B raw39018 raw39018Labels = mixedMoment B raw39018step0 raw39018step0Labels := by
      have ha : raw39018step0 = (fun i j => raw39018 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39018step0 raw39018; decide +kernel
      have hl : raw39018step0Labels = raw39018Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39018 raw39018Labels permutation32 permutation7
    mixedMoment B raw39018step0 raw39018step0Labels = mixedMoment B raw39018step1 raw39018step1Labels := by
      have ha : raw39018step1 = -raw39018step0 := by apply Matrix.ext; change ∀ i j, raw39018step1 i j = -(raw39018step0 i j); unfold raw39018step1 raw39018step0; decide +kernel
      have hl : raw39018step1Labels = raw39018step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39018step1 raw39018step1Labels = mixedMoment B raw39018step2 raw39018step2Labels := by
      have ha : raw39018step2 = raw39018step1 := by apply Matrix.ext; unfold raw39018step2 raw39018step1; decide +kernel
      have hl : raw39018step1Labels = labelEmbedding1 ∘ raw39018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39018step1 raw39018step1Labels raw39018step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3592 node3592Labels := by rfl

def raw39019 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39019 raw39019Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw39019 raw39019Labels = mixedMoment B raw39019step0 raw39019step0Labels := by
      have ha : raw39019step0 = (fun i j => raw39019 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39019step0 raw39019; decide +kernel
      have hl : raw39019step0Labels = raw39019Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39019 raw39019Labels permutation33 permutation3
    _ = mixedMoment B node2813 node2813Labels := by rfl

def raw39020 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39020Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw39020step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw39020step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw39020step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39020 raw39020Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw39020 raw39020Labels = mixedMoment B raw39020step0 raw39020step0Labels := by
      have ha : raw39020step0 = (fun i j => raw39020 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39020step0 raw39020; decide +kernel
      have hl : raw39020step0Labels = raw39020Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39020 raw39020Labels permutation34 permutation7
    mixedMoment B raw39020step0 raw39020step0Labels = mixedMoment B raw39020step1 raw39020step1Labels := by
      have ha : raw39020step1 = -raw39020step0 := by apply Matrix.ext; change ∀ i j, raw39020step1 i j = -(raw39020step0 i j); unfold raw39020step1 raw39020step0; decide +kernel
      have hl : raw39020step1Labels = raw39020step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39020step1 raw39020step1Labels = mixedMoment B raw39020step2 raw39020step2Labels := by
      have ha : raw39020step2 = raw39020step1 := by apply Matrix.ext; unfold raw39020step2 raw39020step1; decide +kernel
      have hl : raw39020step1Labels = labelEmbedding1 ∘ raw39020step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39020step1 raw39020step1Labels raw39020step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

def raw39021 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw39021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39021 raw39021Labels = mixedMoment B node2805 node2805Labels := by
  calc
    mixedMoment B raw39021 raw39021Labels = mixedMoment B raw39021step0 raw39021step0Labels := by
      have ha : raw39021step0 = (fun i j => raw39021 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39021step0 raw39021; decide +kernel
      have hl : raw39021step0Labels = raw39021Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39021 raw39021Labels permutation32 permutation3
    _ = mixedMoment B node2805 node2805Labels := by rfl

def raw39022 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw39022Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![0, -2, 2], ![-2, 1, 1]]
def raw39022step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def raw39022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def raw39022step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39022 raw39022Labels = mixedMoment B node3594 node3594Labels := by
  calc
    mixedMoment B raw39022 raw39022Labels = mixedMoment B raw39022step0 raw39022step0Labels := by
      have ha : raw39022step0 = (fun i j => raw39022 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39022step0 raw39022; decide +kernel
      have hl : raw39022step0Labels = raw39022Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39022 raw39022Labels permutation35 permutation7
    mixedMoment B raw39022step0 raw39022step0Labels = mixedMoment B raw39022step1 raw39022step1Labels := by
      have ha : raw39022step1 = -raw39022step0 := by apply Matrix.ext; change ∀ i j, raw39022step1 i j = -(raw39022step0 i j); unfold raw39022step1 raw39022step0; decide +kernel
      have hl : raw39022step1Labels = raw39022step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39022step1 raw39022step1Labels = mixedMoment B raw39022step2 raw39022step2Labels := by
      have ha : raw39022step2 = raw39022step1 := by apply Matrix.ext; unfold raw39022step2 raw39022step1; decide +kernel
      have hl : raw39022step1Labels = labelEmbedding1 ∘ raw39022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39022step1 raw39022step1Labels raw39022step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3594 node3594Labels := by rfl

def raw39023 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw39023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39023step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw39023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39023 raw39023Labels = mixedMoment B node2820 node2820Labels := by
  calc
    mixedMoment B raw39023 raw39023Labels = mixedMoment B raw39023step0 raw39023step0Labels := by
      have ha : raw39023step0 = (fun i j => raw39023 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39023step0 raw39023; decide +kernel
      have hl : raw39023step0Labels = raw39023Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39023 raw39023Labels permutation8 permutation3
    _ = mixedMoment B node2820 node2820Labels := by rfl

def raw39024 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw39024Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39024step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw39024step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw39024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39024 raw39024Labels = mixedMoment B node3596 node3596Labels := by
  calc
    mixedMoment B raw39024 raw39024Labels = mixedMoment B raw39024step0 raw39024step0Labels := by
      have ha : raw39024step0 = (fun i j => raw39024 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39024step0 raw39024; decide +kernel
      have hl : raw39024step0Labels = raw39024Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39024 raw39024Labels permutation31 permutation7
    mixedMoment B raw39024step0 raw39024step0Labels = mixedMoment B raw39024step1 raw39024step1Labels := by
      have ha : raw39024step1 = raw39024step0 := by apply Matrix.ext; unfold raw39024step1 raw39024step0; decide +kernel
      have hl : raw39024step0Labels = labelEmbedding1 ∘ raw39024step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39024step0 raw39024step0Labels raw39024step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3596 node3596Labels := by rfl

def raw39025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39025Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39025step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39025step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39025step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39025step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39025 raw39025Labels = mixedMoment B node2366 node2366Labels := by
  calc
    mixedMoment B raw39025 raw39025Labels = mixedMoment B raw39025step0 raw39025step0Labels := by
      have ha : raw39025step0 = (fun i j => raw39025 (permutation265 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39025step0 raw39025; decide +kernel
      have hl : raw39025step0Labels = raw39025Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39025 raw39025Labels permutation265 permutation5
    mixedMoment B raw39025step0 raw39025step0Labels = mixedMoment B raw39025step1 raw39025step1Labels := by
      have ha : raw39025step1 = -raw39025step0 := by apply Matrix.ext; change ∀ i j, raw39025step1 i j = -(raw39025step0 i j); unfold raw39025step1 raw39025step0; decide +kernel
      have hl : raw39025step1Labels = raw39025step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39025step1 raw39025step1Labels = mixedMoment B raw39025step2 raw39025step2Labels := by
      have ha : raw39025step2 = raw39025step1 := by apply Matrix.ext; unfold raw39025step2 raw39025step1; decide +kernel
      have hl : raw39025step1Labels = labelEmbedding1 ∘ raw39025step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39025step1 raw39025step1Labels raw39025step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2366 node2366Labels := by rfl

def raw39026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39026Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw39026step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39026step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39026step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39026step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39026 raw39026Labels = mixedMoment B node2364 node2364Labels := by
  calc
    mixedMoment B raw39026 raw39026Labels = mixedMoment B raw39026step0 raw39026step0Labels := by
      have ha : raw39026step0 = (fun i j => raw39026 (permutation277 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39026step0 raw39026; decide +kernel
      have hl : raw39026step0Labels = raw39026Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39026 raw39026Labels permutation277 permutation5
    mixedMoment B raw39026step0 raw39026step0Labels = mixedMoment B raw39026step1 raw39026step1Labels := by
      have ha : raw39026step1 = -raw39026step0 := by apply Matrix.ext; change ∀ i j, raw39026step1 i j = -(raw39026step0 i j); unfold raw39026step1 raw39026step0; decide +kernel
      have hl : raw39026step1Labels = raw39026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39026step1 raw39026step1Labels = mixedMoment B raw39026step2 raw39026step2Labels := by
      have ha : raw39026step2 = raw39026step1 := by apply Matrix.ext; unfold raw39026step2 raw39026step1; decide +kernel
      have hl : raw39026step1Labels = labelEmbedding1 ∘ raw39026step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39026step1 raw39026step1Labels raw39026step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2364 node2364Labels := by rfl

def raw39027 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw39027Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![-3, 2, 1]]
def raw39027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw39027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw39027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39027 raw39027Labels = mixedMoment B node2421 node2421Labels := by
  calc
    mixedMoment B raw39027 raw39027Labels = mixedMoment B raw39027step0 raw39027step0Labels := by
      have ha : raw39027step0 = (fun i j => raw39027 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39027step0 raw39027; decide +kernel
      have hl : raw39027step0Labels = raw39027Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39027 raw39027Labels permutation145 permutation3
    mixedMoment B raw39027step0 raw39027step0Labels = mixedMoment B raw39027step1 raw39027step1Labels := by
      have ha : raw39027step1 = -raw39027step0 := by apply Matrix.ext; change ∀ i j, raw39027step1 i j = -(raw39027step0 i j); unfold raw39027step1 raw39027step0; decide +kernel
      have hl : raw39027step1Labels = raw39027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2421 node2421Labels := by rfl

def raw39028 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw39028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw39028step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw39028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw39028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39028 raw39028Labels = mixedMoment B node2367 node2367Labels := by
  calc
    mixedMoment B raw39028 raw39028Labels = mixedMoment B raw39028step0 raw39028step0Labels := by
      have ha : raw39028step0 = (fun i j => raw39028 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39028step0 raw39028; decide +kernel
      have hl : raw39028step0Labels = raw39028Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39028 raw39028Labels permutation56 permutation5
    mixedMoment B raw39028step0 raw39028step0Labels = mixedMoment B raw39028step1 raw39028step1Labels := by
      have ha : raw39028step1 = -raw39028step0 := by apply Matrix.ext; change ∀ i j, raw39028step1 i j = -(raw39028step0 i j); unfold raw39028step1 raw39028step0; decide +kernel
      have hl : raw39028step1Labels = raw39028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39028step1 raw39028step1Labels = mixedMoment B raw39028step2 raw39028step2Labels := by
      have ha : raw39028step2 = raw39028step1 := by apply Matrix.ext; unfold raw39028step2 raw39028step1; decide +kernel
      have hl : raw39028step1Labels = labelEmbedding1 ∘ raw39028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39028step1 raw39028step1Labels raw39028step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2367 node2367Labels := by rfl

def raw39029 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw39029Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39029 raw39029Labels = mixedMoment B node2794 node2794Labels := by
  calc
    mixedMoment B raw39029 raw39029Labels = mixedMoment B raw39029step0 raw39029step0Labels := by
      have ha : raw39029step0 = (fun i j => raw39029 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39029step0 raw39029; decide +kernel
      have hl : raw39029step0Labels = raw39029Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39029 raw39029Labels permutation33 permutation3
    _ = mixedMoment B node2794 node2794Labels := by rfl

def raw39030 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw39030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw39030step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39030 raw39030Labels = mixedMoment B node2368 node2368Labels := by
  calc
    mixedMoment B raw39030 raw39030Labels = mixedMoment B raw39030step0 raw39030step0Labels := by
      have ha : raw39030step0 = (fun i j => raw39030 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39030step0 raw39030; decide +kernel
      have hl : raw39030step0Labels = raw39030Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39030 raw39030Labels permutation57 permutation5
    mixedMoment B raw39030step0 raw39030step0Labels = mixedMoment B raw39030step1 raw39030step1Labels := by
      have ha : raw39030step1 = -raw39030step0 := by apply Matrix.ext; change ∀ i j, raw39030step1 i j = -(raw39030step0 i j); unfold raw39030step1 raw39030step0; decide +kernel
      have hl : raw39030step1Labels = raw39030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39030step1 raw39030step1Labels = mixedMoment B raw39030step2 raw39030step2Labels := by
      have ha : raw39030step2 = raw39030step1 := by apply Matrix.ext; unfold raw39030step2 raw39030step1; decide +kernel
      have hl : raw39030step1Labels = labelEmbedding1 ∘ raw39030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39030step1 raw39030step1Labels raw39030step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2368 node2368Labels := by rfl

def raw39031 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw39031Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw39031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39031 raw39031Labels = mixedMoment B node2792 node2792Labels := by
  calc
    mixedMoment B raw39031 raw39031Labels = mixedMoment B raw39031step0 raw39031step0Labels := by
      have ha : raw39031step0 = (fun i j => raw39031 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39031step0 raw39031; decide +kernel
      have hl : raw39031step0Labels = raw39031Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39031 raw39031Labels permutation32 permutation3
    _ = mixedMoment B node2792 node2792Labels := by rfl

def raw39032 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw39032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw39032step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw39032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw39032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39032 raw39032Labels = mixedMoment B node2365 node2365Labels := by
  calc
    mixedMoment B raw39032 raw39032Labels = mixedMoment B raw39032step0 raw39032step0Labels := by
      have ha : raw39032step0 = (fun i j => raw39032 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39032step0 raw39032; decide +kernel
      have hl : raw39032step0Labels = raw39032Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39032 raw39032Labels permutation56 permutation5
    mixedMoment B raw39032step0 raw39032step0Labels = mixedMoment B raw39032step1 raw39032step1Labels := by
      have ha : raw39032step1 = -raw39032step0 := by apply Matrix.ext; change ∀ i j, raw39032step1 i j = -(raw39032step0 i j); unfold raw39032step1 raw39032step0; decide +kernel
      have hl : raw39032step1Labels = raw39032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39032step1 raw39032step1Labels = mixedMoment B raw39032step2 raw39032step2Labels := by
      have ha : raw39032step2 = raw39032step1 := by apply Matrix.ext; unfold raw39032step2 raw39032step1; decide +kernel
      have hl : raw39032step1Labels = labelEmbedding1 ∘ raw39032step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39032step1 raw39032step1Labels raw39032step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2365 node2365Labels := by rfl

def raw39033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw39033Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw39033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39033 raw39033Labels = mixedMoment B node2370 node2370Labels := by
  calc
    mixedMoment B raw39033 raw39033Labels = mixedMoment B raw39033step0 raw39033step0Labels := by
      have ha : raw39033step0 = raw39033 := by apply Matrix.ext; unfold raw39033step0 raw39033; decide +kernel
      have hl : raw39033Labels = labelEmbedding2 ∘ raw39033step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39033 raw39033Labels raw39033step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2370 node2370Labels := by rfl

def raw39034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw39034Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw39034step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw39034step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39034step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw39034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39034 raw39034Labels = mixedMoment B node3334 node3334Labels := by
  calc
    mixedMoment B raw39034 raw39034Labels = mixedMoment B raw39034step0 raw39034step0Labels := by
      have ha : raw39034step0 = (fun i j => raw39034 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39034step0 raw39034; decide +kernel
      have hl : raw39034step0Labels = raw39034Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39034 raw39034Labels permutation152 permutation7
    mixedMoment B raw39034step0 raw39034step0Labels = mixedMoment B raw39034step1 raw39034step1Labels := by
      have ha : raw39034step1 = -raw39034step0 := by apply Matrix.ext; change ∀ i j, raw39034step1 i j = -(raw39034step0 i j); unfold raw39034step1 raw39034step0; decide +kernel
      have hl : raw39034step1Labels = raw39034step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39034step1 raw39034step1Labels = mixedMoment B raw39034step2 raw39034step2Labels := by
      have ha : raw39034step2 = raw39034step1 := by apply Matrix.ext; unfold raw39034step2 raw39034step1; decide +kernel
      have hl : raw39034step1Labels = labelEmbedding4 ∘ raw39034step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39034step1 raw39034step1Labels raw39034step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3334 node3334Labels := by rfl

def raw39035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw39035Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw39035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39035 raw39035Labels = mixedMoment B node2371 node2371Labels := by
  calc
    mixedMoment B raw39035 raw39035Labels = mixedMoment B raw39035step0 raw39035step0Labels := by
      have ha : raw39035step0 = raw39035 := by apply Matrix.ext; unfold raw39035step0 raw39035; decide +kernel
      have hl : raw39035Labels = labelEmbedding2 ∘ raw39035step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39035 raw39035Labels raw39035step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2371 node2371Labels := by rfl

def raw39036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw39036Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw39036step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw39036step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39036step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw39036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39036 raw39036Labels = mixedMoment B node3335 node3335Labels := by
  calc
    mixedMoment B raw39036 raw39036Labels = mixedMoment B raw39036step0 raw39036step0Labels := by
      have ha : raw39036step0 = (fun i j => raw39036 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39036step0 raw39036; decide +kernel
      have hl : raw39036step0Labels = raw39036Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39036 raw39036Labels permutation152 permutation7
    mixedMoment B raw39036step0 raw39036step0Labels = mixedMoment B raw39036step1 raw39036step1Labels := by
      have ha : raw39036step1 = -raw39036step0 := by apply Matrix.ext; change ∀ i j, raw39036step1 i j = -(raw39036step0 i j); unfold raw39036step1 raw39036step0; decide +kernel
      have hl : raw39036step1Labels = raw39036step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39036step1 raw39036step1Labels = mixedMoment B raw39036step2 raw39036step2Labels := by
      have ha : raw39036step2 = raw39036step1 := by apply Matrix.ext; unfold raw39036step2 raw39036step1; decide +kernel
      have hl : raw39036step1Labels = labelEmbedding4 ∘ raw39036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39036step1 raw39036step1Labels raw39036step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3335 node3335Labels := by rfl

def raw39037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39037Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39037 raw39037Labels = mixedMoment B node2372 node2372Labels := by
  calc
    mixedMoment B raw39037 raw39037Labels = mixedMoment B raw39037step0 raw39037step0Labels := by
      have ha : raw39037step0 = raw39037 := by apply Matrix.ext; unfold raw39037step0 raw39037; decide +kernel
      have hl : raw39037Labels = labelEmbedding2 ∘ raw39037step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39037 raw39037Labels raw39037step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2372 node2372Labels := by rfl

def raw39038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39038Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw39038step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39038step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39038step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39038 raw39038Labels = mixedMoment B node3336 node3336Labels := by
  calc
    mixedMoment B raw39038 raw39038Labels = mixedMoment B raw39038step0 raw39038step0Labels := by
      have ha : raw39038step0 = (fun i j => raw39038 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39038step0 raw39038; decide +kernel
      have hl : raw39038step0Labels = raw39038Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39038 raw39038Labels permutation152 permutation7
    mixedMoment B raw39038step0 raw39038step0Labels = mixedMoment B raw39038step1 raw39038step1Labels := by
      have ha : raw39038step1 = -raw39038step0 := by apply Matrix.ext; change ∀ i j, raw39038step1 i j = -(raw39038step0 i j); unfold raw39038step1 raw39038step0; decide +kernel
      have hl : raw39038step1Labels = raw39038step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39038step1 raw39038step1Labels = mixedMoment B raw39038step2 raw39038step2Labels := by
      have ha : raw39038step2 = raw39038step1 := by apply Matrix.ext; unfold raw39038step2 raw39038step1; decide +kernel
      have hl : raw39038step1Labels = labelEmbedding4 ∘ raw39038step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39038step1 raw39038step1Labels raw39038step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3336 node3336Labels := by rfl

def raw39039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw39039Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw39039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39039 raw39039Labels = mixedMoment B node2373 node2373Labels := by
  calc
    mixedMoment B raw39039 raw39039Labels = mixedMoment B raw39039step0 raw39039step0Labels := by
      have ha : raw39039step0 = raw39039 := by apply Matrix.ext; unfold raw39039step0 raw39039; decide +kernel
      have hl : raw39039Labels = labelEmbedding2 ∘ raw39039step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39039 raw39039Labels raw39039step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2373 node2373Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
