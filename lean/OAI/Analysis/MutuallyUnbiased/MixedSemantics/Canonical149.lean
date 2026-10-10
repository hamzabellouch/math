import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw19072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw19072step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19072step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19072step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19072step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19072 raw19072Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw19072 raw19072Labels = mixedMoment B raw19072step0 raw19072step0Labels := by
      have ha : raw19072step0 = (fun i j => raw19072 (permutation368 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19072step0 raw19072; decide +kernel
      have hl : raw19072step0Labels = raw19072Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19072 raw19072Labels permutation368 permutation5
    mixedMoment B raw19072step0 raw19072step0Labels = mixedMoment B raw19072step1 raw19072step1Labels := by
      have ha : raw19072step1 = -raw19072step0 := by apply Matrix.ext; change ∀ i j, raw19072step1 i j = -(raw19072step0 i j); unfold raw19072step1 raw19072step0; decide +kernel
      have hl : raw19072step1Labels = raw19072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19072step1 raw19072step1Labels = mixedMoment B raw19072step2 raw19072step2Labels := by
      have ha : raw19072step2 = raw19072step1 := by apply Matrix.ext; unfold raw19072step2 raw19072step1; decide +kernel
      have hl : raw19072step1Labels = labelEmbedding8 ∘ raw19072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19072step1 raw19072step1Labels raw19072step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw19073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw19073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19073step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19073 raw19073Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19073 raw19073Labels = mixedMoment B raw19073step0 raw19073step0Labels := by
      have ha : raw19073step0 = (fun i j => raw19073 (permutation589 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19073step0 raw19073; decide +kernel
      have hl : raw19073step0Labels = raw19073Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19073 raw19073Labels permutation589 permutation4
    mixedMoment B raw19073step0 raw19073step0Labels = mixedMoment B raw19073step1 raw19073step1Labels := by
      have ha : raw19073step1 = raw19073step0 := by apply Matrix.ext; unfold raw19073step1 raw19073step0; decide +kernel
      have hl : raw19073step0Labels = labelEmbedding7 ∘ raw19073step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19073step0 raw19073step0Labels raw19073step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw19074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw19074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19074step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19074 raw19074Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19074 raw19074Labels = mixedMoment B raw19074step0 raw19074step0Labels := by
      have ha : raw19074step0 = (fun i j => raw19074 (permutation568 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19074step0 raw19074; decide +kernel
      have hl : raw19074step0Labels = raw19074Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19074 raw19074Labels permutation568 permutation4
    mixedMoment B raw19074step0 raw19074step0Labels = mixedMoment B raw19074step1 raw19074step1Labels := by
      have ha : raw19074step1 = raw19074step0 := by apply Matrix.ext; unfold raw19074step1 raw19074step0; decide +kernel
      have hl : raw19074step0Labels = labelEmbedding7 ∘ raw19074step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19074step0 raw19074step0Labels raw19074step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw19075 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw19075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19075step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19075step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19075step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19075 raw19075Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw19075 raw19075Labels = mixedMoment B raw19075step0 raw19075step0Labels := by
      have ha : raw19075step0 = (fun i j => raw19075 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19075step0 raw19075; decide +kernel
      have hl : raw19075step0Labels = raw19075Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19075 raw19075Labels permutation152 permutation4
    mixedMoment B raw19075step0 raw19075step0Labels = mixedMoment B raw19075step1 raw19075step1Labels := by
      have ha : raw19075step1 = -raw19075step0 := by apply Matrix.ext; change ∀ i j, raw19075step1 i j = -(raw19075step0 i j); unfold raw19075step1 raw19075step0; decide +kernel
      have hl : raw19075step1Labels = raw19075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19075step1 raw19075step1Labels = mixedMoment B raw19075step2 raw19075step2Labels := by
      have ha : raw19075step2 = raw19075step1 := by apply Matrix.ext; unfold raw19075step2 raw19075step1; decide +kernel
      have hl : raw19075step1Labels = labelEmbedding7 ∘ raw19075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19075step1 raw19075step1Labels raw19075step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw19076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw19076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19076step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19076step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19076step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19076 raw19076Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw19076 raw19076Labels = mixedMoment B raw19076step0 raw19076step0Labels := by
      have ha : raw19076step0 = (fun i j => raw19076 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19076step0 raw19076; decide +kernel
      have hl : raw19076step0Labels = raw19076Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19076 raw19076Labels permutation265 permutation4
    mixedMoment B raw19076step0 raw19076step0Labels = mixedMoment B raw19076step1 raw19076step1Labels := by
      have ha : raw19076step1 = -raw19076step0 := by apply Matrix.ext; change ∀ i j, raw19076step1 i j = -(raw19076step0 i j); unfold raw19076step1 raw19076step0; decide +kernel
      have hl : raw19076step1Labels = raw19076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19076step1 raw19076step1Labels = mixedMoment B raw19076step2 raw19076step2Labels := by
      have ha : raw19076step2 = raw19076step1 := by apply Matrix.ext; unfold raw19076step2 raw19076step1; decide +kernel
      have hl : raw19076step1Labels = labelEmbedding7 ∘ raw19076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19076step1 raw19076step1Labels raw19076step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw19077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw19077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw19077step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19077step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19077step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19077step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19077 raw19077Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw19077 raw19077Labels = mixedMoment B raw19077step0 raw19077step0Labels := by
      have ha : raw19077step0 = (fun i j => raw19077 (permutation367 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19077step0 raw19077; decide +kernel
      have hl : raw19077step0Labels = raw19077Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19077 raw19077Labels permutation367 permutation5
    mixedMoment B raw19077step0 raw19077step0Labels = mixedMoment B raw19077step1 raw19077step1Labels := by
      have ha : raw19077step1 = -raw19077step0 := by apply Matrix.ext; change ∀ i j, raw19077step1 i j = -(raw19077step0 i j); unfold raw19077step1 raw19077step0; decide +kernel
      have hl : raw19077step1Labels = raw19077step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19077step1 raw19077step1Labels = mixedMoment B raw19077step2 raw19077step2Labels := by
      have ha : raw19077step2 = raw19077step1 := by apply Matrix.ext; unfold raw19077step2 raw19077step1; decide +kernel
      have hl : raw19077step1Labels = labelEmbedding8 ∘ raw19077step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19077step1 raw19077step1Labels raw19077step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw19078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw19078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19078step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19078step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19078 raw19078Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19078 raw19078Labels = mixedMoment B raw19078step0 raw19078step0Labels := by
      have ha : raw19078step0 = (fun i j => raw19078 (permutation688 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19078step0 raw19078; decide +kernel
      have hl : raw19078step0Labels = raw19078Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19078 raw19078Labels permutation688 permutation4
    mixedMoment B raw19078step0 raw19078step0Labels = mixedMoment B raw19078step1 raw19078step1Labels := by
      have ha : raw19078step1 = raw19078step0 := by apply Matrix.ext; unfold raw19078step1 raw19078step0; decide +kernel
      have hl : raw19078step0Labels = labelEmbedding7 ∘ raw19078step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19078step0 raw19078step0Labels raw19078step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw19079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw19079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19079step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19079 raw19079Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19079 raw19079Labels = mixedMoment B raw19079step0 raw19079step0Labels := by
      have ha : raw19079step0 = (fun i j => raw19079 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19079step0 raw19079; decide +kernel
      have hl : raw19079step0Labels = raw19079Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19079 raw19079Labels permutation664 permutation4
    mixedMoment B raw19079step0 raw19079step0Labels = mixedMoment B raw19079step1 raw19079step1Labels := by
      have ha : raw19079step1 = raw19079step0 := by apply Matrix.ext; unfold raw19079step1 raw19079step0; decide +kernel
      have hl : raw19079step0Labels = labelEmbedding7 ∘ raw19079step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19079step0 raw19079step0Labels raw19079step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw19080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19080 raw19080Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw19080 raw19080Labels = mixedMoment B raw19080step0 raw19080step0Labels := by
      have ha : raw19080step0 = (fun i j => raw19080 (permutation269 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19080step0 raw19080; decide +kernel
      have hl : raw19080step0Labels = raw19080Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19080 raw19080Labels permutation269 permutation2
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw19081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19081step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19081step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19081step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19081 raw19081Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw19081 raw19081Labels = mixedMoment B raw19081step0 raw19081step0Labels := by
      have ha : raw19081step0 = (fun i j => raw19081 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19081step0 raw19081; decide +kernel
      have hl : raw19081step0Labels = raw19081Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19081 raw19081Labels permutation283 permutation7
    mixedMoment B raw19081step0 raw19081step0Labels = mixedMoment B raw19081step1 raw19081step1Labels := by
      have ha : raw19081step1 = -raw19081step0 := by apply Matrix.ext; change ∀ i j, raw19081step1 i j = -(raw19081step0 i j); unfold raw19081step1 raw19081step0; decide +kernel
      have hl : raw19081step1Labels = raw19081step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19081step1 raw19081step1Labels = mixedMoment B raw19081step2 raw19081step2Labels := by
      have ha : raw19081step2 = raw19081step1 := by apply Matrix.ext; unfold raw19081step2 raw19081step1; decide +kernel
      have hl : raw19081step1Labels = labelEmbedding10 ∘ raw19081step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19081step1 raw19081step1Labels raw19081step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw19082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19082step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19082step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19082step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19082 raw19082Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19082 raw19082Labels = mixedMoment B raw19082step0 raw19082step0Labels := by
      have ha : raw19082step0 = (fun i j => raw19082 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19082step0 raw19082; decide +kernel
      have hl : raw19082step0Labels = raw19082Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19082 raw19082Labels permutation283 permutation7
    mixedMoment B raw19082step0 raw19082step0Labels = mixedMoment B raw19082step1 raw19082step1Labels := by
      have ha : raw19082step1 = -raw19082step0 := by apply Matrix.ext; change ∀ i j, raw19082step1 i j = -(raw19082step0 i j); unfold raw19082step1 raw19082step0; decide +kernel
      have hl : raw19082step1Labels = raw19082step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19082step1 raw19082step1Labels = mixedMoment B raw19082step2 raw19082step2Labels := by
      have ha : raw19082step2 = raw19082step1 := by apply Matrix.ext; unfold raw19082step2 raw19082step1; decide +kernel
      have hl : raw19082step1Labels = labelEmbedding10 ∘ raw19082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19082step1 raw19082step1Labels raw19082step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19083step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19083step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19083step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19083step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19083 raw19083Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19083 raw19083Labels = mixedMoment B raw19083step0 raw19083step0Labels := by
      have ha : raw19083step0 = (fun i j => raw19083 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19083step0 raw19083; decide +kernel
      have hl : raw19083step0Labels = raw19083Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19083 raw19083Labels permutation284 permutation7
    mixedMoment B raw19083step0 raw19083step0Labels = mixedMoment B raw19083step1 raw19083step1Labels := by
      have ha : raw19083step1 = -raw19083step0 := by apply Matrix.ext; change ∀ i j, raw19083step1 i j = -(raw19083step0 i j); unfold raw19083step1 raw19083step0; decide +kernel
      have hl : raw19083step1Labels = raw19083step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19083step1 raw19083step1Labels = mixedMoment B raw19083step2 raw19083step2Labels := by
      have ha : raw19083step2 = raw19083step1 := by apply Matrix.ext; unfold raw19083step2 raw19083step1; decide +kernel
      have hl : raw19083step1Labels = labelEmbedding10 ∘ raw19083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19083step1 raw19083step1Labels raw19083step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19084step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19084step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19084step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19084step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19084 raw19084Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw19084 raw19084Labels = mixedMoment B raw19084step0 raw19084step0Labels := by
      have hz : ∀ j, raw19084 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19084step0 = (fun i j => raw19084 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19084step0 raw19084; decide +kernel
      have hl : raw19084step0Labels = raw19084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19084 raw19084Labels permutation590 hz
    mixedMoment B raw19084step0 raw19084step0Labels = mixedMoment B raw19084step1 raw19084step1Labels := by
      have ha : raw19084step1 = (fun i j => raw19084step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19084step1 raw19084step0; decide +kernel
      have hl : raw19084step1Labels = raw19084step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19084step0 raw19084step0Labels permutation56 permutation7
    mixedMoment B raw19084step1 raw19084step1Labels = mixedMoment B raw19084step2 raw19084step2Labels := by
      have ha : raw19084step2 = -raw19084step1 := by apply Matrix.ext; change ∀ i j, raw19084step2 i j = -(raw19084step1 i j); unfold raw19084step2 raw19084step1; decide +kernel
      have hl : raw19084step2Labels = raw19084step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19084step2 raw19084step2Labels = mixedMoment B raw19084step3 raw19084step3Labels := by
      have ha : raw19084step3 = raw19084step2 := by apply Matrix.ext; unfold raw19084step3 raw19084step2; decide +kernel
      have hl : raw19084step2Labels = labelEmbedding10 ∘ raw19084step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19084step2 raw19084step2Labels raw19084step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw19085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19085step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19085 raw19085Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw19085 raw19085Labels = mixedMoment B raw19085step0 raw19085step0Labels := by
      have ha : raw19085step0 = (fun i j => raw19085 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19085step0 raw19085; decide +kernel
      have hl : raw19085step0Labels = raw19085Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19085 raw19085Labels permutation176 permutation3
    mixedMoment B raw19085step0 raw19085step0Labels = mixedMoment B raw19085step1 raw19085step1Labels := by
      have ha : raw19085step1 = raw19085step0 := by apply Matrix.ext; unfold raw19085step1 raw19085step0; decide +kernel
      have hl : raw19085step0Labels = labelEmbedding6 ∘ raw19085step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19085step0 raw19085step0Labels raw19085step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw19086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19086step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19086 raw19086Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw19086 raw19086Labels = mixedMoment B raw19086step0 raw19086step0Labels := by
      have ha : raw19086step0 = (fun i j => raw19086 (permutation342 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19086step0 raw19086; decide +kernel
      have hl : raw19086step0Labels = raw19086Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19086 raw19086Labels permutation342 permutation4
    mixedMoment B raw19086step0 raw19086step0Labels = mixedMoment B raw19086step1 raw19086step1Labels := by
      have ha : raw19086step1 = raw19086step0 := by apply Matrix.ext; unfold raw19086step1 raw19086step0; decide +kernel
      have hl : raw19086step0Labels = labelEmbedding7 ∘ raw19086step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19086step0 raw19086step0Labels raw19086step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw19087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19087step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19087 raw19087Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw19087 raw19087Labels = mixedMoment B raw19087step0 raw19087step0Labels := by
      have ha : raw19087step0 = (fun i j => raw19087 (permutation344 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19087step0 raw19087; decide +kernel
      have hl : raw19087step0Labels = raw19087Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19087 raw19087Labels permutation344 permutation4
    mixedMoment B raw19087step0 raw19087step0Labels = mixedMoment B raw19087step1 raw19087step1Labels := by
      have ha : raw19087step1 = raw19087step0 := by apply Matrix.ext; unfold raw19087step1 raw19087step0; decide +kernel
      have hl : raw19087step0Labels = labelEmbedding7 ∘ raw19087step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19087step0 raw19087step0Labels raw19087step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw19088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19088step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19088 raw19088Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw19088 raw19088Labels = mixedMoment B raw19088step0 raw19088step0Labels := by
      have ha : raw19088step0 = (fun i j => raw19088 (permutation341 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19088step0 raw19088; decide +kernel
      have hl : raw19088step0Labels = raw19088Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19088 raw19088Labels permutation341 permutation4
    mixedMoment B raw19088step0 raw19088step0Labels = mixedMoment B raw19088step1 raw19088step1Labels := by
      have ha : raw19088step1 = raw19088step0 := by apply Matrix.ext; unfold raw19088step1 raw19088step0; decide +kernel
      have hl : raw19088step0Labels = labelEmbedding7 ∘ raw19088step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19088step0 raw19088step0Labels raw19088step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw19089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19089step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19089step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19089step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19089 raw19089Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw19089 raw19089Labels = mixedMoment B raw19089step0 raw19089step0Labels := by
      have hz : ∀ j, raw19089 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19089step0 = (fun i j => raw19089 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19089step0 raw19089; decide +kernel
      have hl : raw19089step0Labels = raw19089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19089 raw19089Labels permutation590 hz
    mixedMoment B raw19089step0 raw19089step0Labels = mixedMoment B raw19089step1 raw19089step1Labels := by
      have ha : raw19089step1 = (fun i j => raw19089step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19089step1 raw19089step0; decide +kernel
      have hl : raw19089step1Labels = raw19089step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19089step0 raw19089step0Labels permutation59 permutation6
    mixedMoment B raw19089step1 raw19089step1Labels = mixedMoment B raw19089step2 raw19089step2Labels := by
      have ha : raw19089step2 = -raw19089step1 := by apply Matrix.ext; change ∀ i j, raw19089step2 i j = -(raw19089step1 i j); unfold raw19089step2 raw19089step1; decide +kernel
      have hl : raw19089step2Labels = raw19089step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19089step2 raw19089step2Labels = mixedMoment B raw19089step3 raw19089step3Labels := by
      have ha : raw19089step3 = raw19089step2 := by apply Matrix.ext; unfold raw19089step3 raw19089step2; decide +kernel
      have hl : raw19089step2Labels = labelEmbedding9 ∘ raw19089step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19089step2 raw19089step2Labels raw19089step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw19090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19090step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19090 raw19090Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw19090 raw19090Labels = mixedMoment B raw19090step0 raw19090step0Labels := by
      have ha : raw19090step0 = (fun i j => raw19090 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19090step0 raw19090; decide +kernel
      have hl : raw19090step0Labels = raw19090Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19090 raw19090Labels permutation152 permutation3
    mixedMoment B raw19090step0 raw19090step0Labels = mixedMoment B raw19090step1 raw19090step1Labels := by
      have ha : raw19090step1 = raw19090step0 := by apply Matrix.ext; unfold raw19090step1 raw19090step0; decide +kernel
      have hl : raw19090step0Labels = labelEmbedding6 ∘ raw19090step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19090step0 raw19090step0Labels raw19090step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw19091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19091 raw19091Labels = mixedMoment B node5366 node5366Labels := by
  calc
    mixedMoment B raw19091 raw19091Labels = mixedMoment B raw19091step0 raw19091step0Labels := by
      have ha : raw19091step0 = (fun i j => raw19091 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19091step0 raw19091; decide +kernel
      have hl : raw19091step0Labels = raw19091Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19091 raw19091Labels permutation283 permutation2
    _ = mixedMoment B node5366 node5366Labels := by rfl

def raw19092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19092 raw19092Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw19092 raw19092Labels = mixedMoment B raw19092step0 raw19092step0Labels := by
      have ha : raw19092step0 = (fun i j => raw19092 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19092step0 raw19092; decide +kernel
      have hl : raw19092step0Labels = raw19092Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19092 raw19092Labels permutation162 permutation2
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw19093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19093 raw19093Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw19093 raw19093Labels = mixedMoment B raw19093step0 raw19093step0Labels := by
      have ha : raw19093step0 = (fun i j => raw19093 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19093step0 raw19093; decide +kernel
      have hl : raw19093step0Labels = raw19093Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19093 raw19093Labels permutation168 permutation2
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw19094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19094 raw19094Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw19094 raw19094Labels = mixedMoment B raw19094step0 raw19094step0Labels := by
      have hz : ∀ j, raw19094 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19094step0 = (fun i j => raw19094 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19094step0 raw19094; decide +kernel
      have hl : raw19094step0Labels = raw19094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19094 raw19094Labels permutation590 hz
    _ = mixedMoment B node5474 node5474Labels := by rfl

def raw19095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19095step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19095 raw19095Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw19095 raw19095Labels = mixedMoment B raw19095step0 raw19095step0Labels := by
      have ha : raw19095step0 = (fun i j => raw19095 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19095step0 raw19095; decide +kernel
      have hl : raw19095step0Labels = raw19095Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19095 raw19095Labels permutation155 permutation3
    mixedMoment B raw19095step0 raw19095step0Labels = mixedMoment B raw19095step1 raw19095step1Labels := by
      have ha : raw19095step1 = raw19095step0 := by apply Matrix.ext; unfold raw19095step1 raw19095step0; decide +kernel
      have hl : raw19095step0Labels = labelEmbedding6 ∘ raw19095step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19095step0 raw19095step0Labels raw19095step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw19096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19096 raw19096Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw19096 raw19096Labels = mixedMoment B raw19096step0 raw19096step0Labels := by
      have ha : raw19096step0 = (fun i j => raw19096 (permutation270 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19096step0 raw19096; decide +kernel
      have hl : raw19096step0Labels = raw19096Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19096 raw19096Labels permutation270 permutation2
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw19097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19097 raw19097Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw19097 raw19097Labels = mixedMoment B raw19097step0 raw19097step0Labels := by
      have ha : raw19097step0 = (fun i j => raw19097 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19097step0 raw19097; decide +kernel
      have hl : raw19097step0Labels = raw19097Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19097 raw19097Labels permutation157 permutation2
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw19098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19098 raw19098Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw19098 raw19098Labels = mixedMoment B raw19098step0 raw19098step0Labels := by
      have ha : raw19098step0 = (fun i j => raw19098 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19098step0 raw19098; decide +kernel
      have hl : raw19098step0Labels = raw19098Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19098 raw19098Labels permutation155 permutation2
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw19099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw19099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19099 raw19099Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw19099 raw19099Labels = mixedMoment B raw19099step0 raw19099step0Labels := by
      have hz : ∀ j, raw19099 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19099step0 = (fun i j => raw19099 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19099step0 raw19099; decide +kernel
      have hl : raw19099step0Labels = raw19099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19099 raw19099Labels permutation590 hz
    mixedMoment B raw19099step0 raw19099step0Labels = mixedMoment B raw19099step1 raw19099step1Labels := by
      have ha : raw19099step1 = (fun i j => raw19099step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19099step1 raw19099step0; decide +kernel
      have hl : raw19099step1Labels = raw19099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19099step0 raw19099step0Labels permutation33 permutation2
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw19100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19100step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19100 raw19100Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw19100 raw19100Labels = mixedMoment B raw19100step0 raw19100step0Labels := by
      have ha : raw19100step0 = (fun i j => raw19100 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19100step0 raw19100; decide +kernel
      have hl : raw19100step0Labels = raw19100Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19100 raw19100Labels permutation153 permutation3
    mixedMoment B raw19100step0 raw19100step0Labels = mixedMoment B raw19100step1 raw19100step1Labels := by
      have ha : raw19100step1 = raw19100step0 := by apply Matrix.ext; unfold raw19100step1 raw19100step0; decide +kernel
      have hl : raw19100step0Labels = labelEmbedding6 ∘ raw19100step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19100step0 raw19100step0Labels raw19100step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw19101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19101 raw19101Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw19101 raw19101Labels = mixedMoment B raw19101step0 raw19101step0Labels := by
      have ha : raw19101step0 = (fun i j => raw19101 (permutation269 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19101step0 raw19101; decide +kernel
      have hl : raw19101step0Labels = raw19101Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19101 raw19101Labels permutation269 permutation2
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw19102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19102 raw19102Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw19102 raw19102Labels = mixedMoment B raw19102step0 raw19102step0Labels := by
      have ha : raw19102step0 = (fun i j => raw19102 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19102step0 raw19102; decide +kernel
      have hl : raw19102step0Labels = raw19102Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19102 raw19102Labels permutation156 permutation2
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw19103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19103 raw19103Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw19103 raw19103Labels = mixedMoment B raw19103step0 raw19103step0Labels := by
      have ha : raw19103step0 = (fun i j => raw19103 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19103step0 raw19103; decide +kernel
      have hl : raw19103step0Labels = raw19103Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19103 raw19103Labels permutation153 permutation2
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw19104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19104 raw19104Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw19104 raw19104Labels = mixedMoment B raw19104step0 raw19104step0Labels := by
      have hz : ∀ j, raw19104 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19104step0 = (fun i j => raw19104 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19104step0 raw19104; decide +kernel
      have hl : raw19104step0Labels = raw19104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19104 raw19104Labels permutation590 hz
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw19105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19105step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19105 raw19105Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw19105 raw19105Labels = mixedMoment B raw19105step0 raw19105step0Labels := by
      have ha : raw19105step0 = (fun i j => raw19105 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19105step0 raw19105; decide +kernel
      have hl : raw19105step0Labels = raw19105Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19105 raw19105Labels permutation152 permutation3
    mixedMoment B raw19105step0 raw19105step0Labels = mixedMoment B raw19105step1 raw19105step1Labels := by
      have ha : raw19105step1 = raw19105step0 := by apply Matrix.ext; unfold raw19105step1 raw19105step0; decide +kernel
      have hl : raw19105step0Labels = labelEmbedding6 ∘ raw19105step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19105step0 raw19105step0Labels raw19105step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

def raw19106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19106 raw19106Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw19106 raw19106Labels = mixedMoment B raw19106step0 raw19106step0Labels := by
      have ha : raw19106step0 = (fun i j => raw19106 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19106step0 raw19106; decide +kernel
      have hl : raw19106step0Labels = raw19106Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19106 raw19106Labels permutation265 permutation2
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw19107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw19107step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19107step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19107step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19107 raw19107Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw19107 raw19107Labels = mixedMoment B raw19107step0 raw19107step0Labels := by
      have ha : raw19107step0 = (fun i j => raw19107 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19107step0 raw19107; decide +kernel
      have hl : raw19107step0Labels = raw19107Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19107 raw19107Labels permutation662 permutation3
    mixedMoment B raw19107step0 raw19107step0Labels = mixedMoment B raw19107step1 raw19107step1Labels := by
      have ha : raw19107step1 = -raw19107step0 := by apply Matrix.ext; change ∀ i j, raw19107step1 i j = -(raw19107step0 i j); unfold raw19107step1 raw19107step0; decide +kernel
      have hl : raw19107step1Labels = raw19107step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19107step1 raw19107step1Labels = mixedMoment B raw19107step2 raw19107step2Labels := by
      have ha : raw19107step2 = raw19107step1 := by apply Matrix.ext; unfold raw19107step2 raw19107step1; decide +kernel
      have hl : raw19107step1Labels = labelEmbedding6 ∘ raw19107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19107step1 raw19107step1Labels raw19107step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw19108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw19108step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19108step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19108step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19108 raw19108Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw19108 raw19108Labels = mixedMoment B raw19108step0 raw19108step0Labels := by
      have ha : raw19108step0 = (fun i j => raw19108 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19108step0 raw19108; decide +kernel
      have hl : raw19108step0Labels = raw19108Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19108 raw19108Labels permutation682 permutation3
    mixedMoment B raw19108step0 raw19108step0Labels = mixedMoment B raw19108step1 raw19108step1Labels := by
      have ha : raw19108step1 = -raw19108step0 := by apply Matrix.ext; change ∀ i j, raw19108step1 i j = -(raw19108step0 i j); unfold raw19108step1 raw19108step0; decide +kernel
      have hl : raw19108step1Labels = raw19108step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19108step1 raw19108step1Labels = mixedMoment B raw19108step2 raw19108step2Labels := by
      have ha : raw19108step2 = raw19108step1 := by apply Matrix.ext; unfold raw19108step2 raw19108step1; decide +kernel
      have hl : raw19108step1Labels = labelEmbedding6 ∘ raw19108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19108step1 raw19108step1Labels raw19108step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw19109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw19109step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19109step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19109step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19109 raw19109Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw19109 raw19109Labels = mixedMoment B raw19109step0 raw19109step0Labels := by
      have ha : raw19109step0 = (fun i j => raw19109 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19109step0 raw19109; decide +kernel
      have hl : raw19109step0Labels = raw19109Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19109 raw19109Labels permutation658 permutation3
    mixedMoment B raw19109step0 raw19109step0Labels = mixedMoment B raw19109step1 raw19109step1Labels := by
      have ha : raw19109step1 = -raw19109step0 := by apply Matrix.ext; change ∀ i j, raw19109step1 i j = -(raw19109step0 i j); unfold raw19109step1 raw19109step0; decide +kernel
      have hl : raw19109step1Labels = raw19109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19109step1 raw19109step1Labels = mixedMoment B raw19109step2 raw19109step2Labels := by
      have ha : raw19109step2 = raw19109step1 := by apply Matrix.ext; unfold raw19109step2 raw19109step1; decide +kernel
      have hl : raw19109step1Labels = labelEmbedding6 ∘ raw19109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19109step1 raw19109step1Labels raw19109step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw19110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19110step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19110 raw19110Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw19110 raw19110Labels = mixedMoment B raw19110step0 raw19110step0Labels := by
      have ha : raw19110step0 = (fun i j => raw19110 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19110step0 raw19110; decide +kernel
      have hl : raw19110step0Labels = raw19110Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19110 raw19110Labels permutation283 permutation7
    mixedMoment B raw19110step0 raw19110step0Labels = mixedMoment B raw19110step1 raw19110step1Labels := by
      have ha : raw19110step1 = -raw19110step0 := by apply Matrix.ext; change ∀ i j, raw19110step1 i j = -(raw19110step0 i j); unfold raw19110step1 raw19110step0; decide +kernel
      have hl : raw19110step1Labels = raw19110step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19110step1 raw19110step1Labels = mixedMoment B raw19110step2 raw19110step2Labels := by
      have ha : raw19110step2 = raw19110step1 := by apply Matrix.ext; unfold raw19110step2 raw19110step1; decide +kernel
      have hl : raw19110step1Labels = labelEmbedding1 ∘ raw19110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19110step1 raw19110step1Labels raw19110step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

def raw19111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19111step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19111step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19111step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19111 raw19111Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw19111 raw19111Labels = mixedMoment B raw19111step0 raw19111step0Labels := by
      have ha : raw19111step0 = (fun i j => raw19111 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19111step0 raw19111; decide +kernel
      have hl : raw19111step0Labels = raw19111Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19111 raw19111Labels permutation283 permutation7
    mixedMoment B raw19111step0 raw19111step0Labels = mixedMoment B raw19111step1 raw19111step1Labels := by
      have ha : raw19111step1 = -raw19111step0 := by apply Matrix.ext; change ∀ i j, raw19111step1 i j = -(raw19111step0 i j); unfold raw19111step1 raw19111step0; decide +kernel
      have hl : raw19111step1Labels = raw19111step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19111step1 raw19111step1Labels = mixedMoment B raw19111step2 raw19111step2Labels := by
      have ha : raw19111step2 = raw19111step1 := by apply Matrix.ext; unfold raw19111step2 raw19111step1; decide +kernel
      have hl : raw19111step1Labels = labelEmbedding1 ∘ raw19111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19111step1 raw19111step1Labels raw19111step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw19112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19112step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19112 raw19112Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw19112 raw19112Labels = mixedMoment B raw19112step0 raw19112step0Labels := by
      have ha : raw19112step0 = (fun i j => raw19112 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19112step0 raw19112; decide +kernel
      have hl : raw19112step0Labels = raw19112Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19112 raw19112Labels permutation283 permutation7
    mixedMoment B raw19112step0 raw19112step0Labels = mixedMoment B raw19112step1 raw19112step1Labels := by
      have ha : raw19112step1 = -raw19112step0 := by apply Matrix.ext; change ∀ i j, raw19112step1 i j = -(raw19112step0 i j); unfold raw19112step1 raw19112step0; decide +kernel
      have hl : raw19112step1Labels = raw19112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19112step1 raw19112step1Labels = mixedMoment B raw19112step2 raw19112step2Labels := by
      have ha : raw19112step2 = raw19112step1 := by apply Matrix.ext; unfold raw19112step2 raw19112step1; decide +kernel
      have hl : raw19112step1Labels = labelEmbedding1 ∘ raw19112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19112step1 raw19112step1Labels raw19112step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw19113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19113step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19113step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19113step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19113step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19113 raw19113Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw19113 raw19113Labels = mixedMoment B raw19113step0 raw19113step0Labels := by
      have ha : raw19113step0 = (fun i j => raw19113 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19113step0 raw19113; decide +kernel
      have hl : raw19113step0Labels = raw19113Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19113 raw19113Labels permutation284 permutation7
    mixedMoment B raw19113step0 raw19113step0Labels = mixedMoment B raw19113step1 raw19113step1Labels := by
      have ha : raw19113step1 = -raw19113step0 := by apply Matrix.ext; change ∀ i j, raw19113step1 i j = -(raw19113step0 i j); unfold raw19113step1 raw19113step0; decide +kernel
      have hl : raw19113step1Labels = raw19113step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19113step1 raw19113step1Labels = mixedMoment B raw19113step2 raw19113step2Labels := by
      have ha : raw19113step2 = raw19113step1 := by apply Matrix.ext; unfold raw19113step2 raw19113step1; decide +kernel
      have hl : raw19113step1Labels = labelEmbedding1 ∘ raw19113step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19113step1 raw19113step1Labels raw19113step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw19114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19114step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19114step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19114step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19114step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19114 raw19114Labels = mixedMoment B node3985 node3985Labels := by
  calc
    mixedMoment B raw19114 raw19114Labels = mixedMoment B raw19114step0 raw19114step0Labels := by
      have hz : ∀ j, raw19114 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19114step0 = (fun i j => raw19114 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19114step0 raw19114; decide +kernel
      have hl : raw19114step0Labels = raw19114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19114 raw19114Labels permutation590 hz
    mixedMoment B raw19114step0 raw19114step0Labels = mixedMoment B raw19114step1 raw19114step1Labels := by
      have ha : raw19114step1 = (fun i j => raw19114step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19114step1 raw19114step0; decide +kernel
      have hl : raw19114step1Labels = raw19114step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19114step0 raw19114step0Labels permutation56 permutation7
    mixedMoment B raw19114step1 raw19114step1Labels = mixedMoment B raw19114step2 raw19114step2Labels := by
      have ha : raw19114step2 = -raw19114step1 := by apply Matrix.ext; change ∀ i j, raw19114step2 i j = -(raw19114step1 i j); unfold raw19114step2 raw19114step1; decide +kernel
      have hl : raw19114step2Labels = raw19114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19114step2 raw19114step2Labels = mixedMoment B raw19114step3 raw19114step3Labels := by
      have ha : raw19114step3 = raw19114step2 := by apply Matrix.ext; unfold raw19114step3 raw19114step2; decide +kernel
      have hl : raw19114step2Labels = labelEmbedding1 ∘ raw19114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19114step2 raw19114step2Labels raw19114step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3985 node3985Labels := by rfl

def raw19115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19115step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19115step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19115 raw19115Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw19115 raw19115Labels = mixedMoment B raw19115step0 raw19115step0Labels := by
      have ha : raw19115step0 = (fun i j => raw19115 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19115step0 raw19115; decide +kernel
      have hl : raw19115step0Labels = raw19115Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19115 raw19115Labels permutation185 permutation5
    mixedMoment B raw19115step0 raw19115step0Labels = mixedMoment B raw19115step1 raw19115step1Labels := by
      have ha : raw19115step1 = -raw19115step0 := by apply Matrix.ext; change ∀ i j, raw19115step1 i j = -(raw19115step0 i j); unfold raw19115step1 raw19115step0; decide +kernel
      have hl : raw19115step1Labels = raw19115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19115step1 raw19115step1Labels = mixedMoment B raw19115step2 raw19115step2Labels := by
      have ha : raw19115step2 = raw19115step1 := by apply Matrix.ext; unfold raw19115step2 raw19115step1; decide +kernel
      have hl : raw19115step1Labels = labelEmbedding1 ∘ raw19115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19115step1 raw19115step1Labels raw19115step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw19116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19116step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19116step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19116 raw19116Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw19116 raw19116Labels = mixedMoment B raw19116step0 raw19116step0Labels := by
      have ha : raw19116step0 = (fun i j => raw19116 (permutation355 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19116step0 raw19116; decide +kernel
      have hl : raw19116step0Labels = raw19116Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19116 raw19116Labels permutation355 permutation5
    mixedMoment B raw19116step0 raw19116step0Labels = mixedMoment B raw19116step1 raw19116step1Labels := by
      have ha : raw19116step1 = -raw19116step0 := by apply Matrix.ext; change ∀ i j, raw19116step1 i j = -(raw19116step0 i j); unfold raw19116step1 raw19116step0; decide +kernel
      have hl : raw19116step1Labels = raw19116step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19116step1 raw19116step1Labels = mixedMoment B raw19116step2 raw19116step2Labels := by
      have ha : raw19116step2 = raw19116step1 := by apply Matrix.ext; unfold raw19116step2 raw19116step1; decide +kernel
      have hl : raw19116step1Labels = labelEmbedding1 ∘ raw19116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19116step1 raw19116step1Labels raw19116step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw19117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19117step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19117step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19117step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19117step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19117 raw19117Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw19117 raw19117Labels = mixedMoment B raw19117step0 raw19117step0Labels := by
      have ha : raw19117step0 = (fun i j => raw19117 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19117step0 raw19117; decide +kernel
      have hl : raw19117step0Labels = raw19117Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19117 raw19117Labels permutation283 permutation7
    mixedMoment B raw19117step0 raw19117step0Labels = mixedMoment B raw19117step1 raw19117step1Labels := by
      have ha : raw19117step1 = -raw19117step0 := by apply Matrix.ext; change ∀ i j, raw19117step1 i j = -(raw19117step0 i j); unfold raw19117step1 raw19117step0; decide +kernel
      have hl : raw19117step1Labels = raw19117step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19117step1 raw19117step1Labels = mixedMoment B raw19117step2 raw19117step2Labels := by
      have ha : raw19117step2 = raw19117step1 := by apply Matrix.ext; unfold raw19117step2 raw19117step1; decide +kernel
      have hl : raw19117step1Labels = labelEmbedding1 ∘ raw19117step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19117step1 raw19117step1Labels raw19117step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw19118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19118step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19118step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19118step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19118 raw19118Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw19118 raw19118Labels = mixedMoment B raw19118step0 raw19118step0Labels := by
      have ha : raw19118step0 = (fun i j => raw19118 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19118step0 raw19118; decide +kernel
      have hl : raw19118step0Labels = raw19118Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19118 raw19118Labels permutation284 permutation7
    mixedMoment B raw19118step0 raw19118step0Labels = mixedMoment B raw19118step1 raw19118step1Labels := by
      have ha : raw19118step1 = -raw19118step0 := by apply Matrix.ext; change ∀ i j, raw19118step1 i j = -(raw19118step0 i j); unfold raw19118step1 raw19118step0; decide +kernel
      have hl : raw19118step1Labels = raw19118step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19118step1 raw19118step1Labels = mixedMoment B raw19118step2 raw19118step2Labels := by
      have ha : raw19118step2 = raw19118step1 := by apply Matrix.ext; unfold raw19118step2 raw19118step1; decide +kernel
      have hl : raw19118step1Labels = labelEmbedding1 ∘ raw19118step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19118step1 raw19118step1Labels raw19118step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw19119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19119step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19119step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19119 raw19119Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw19119 raw19119Labels = mixedMoment B raw19119step0 raw19119step0Labels := by
      have hz : ∀ j, raw19119 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19119step0 = (fun i j => raw19119 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19119step0 raw19119; decide +kernel
      have hl : raw19119step0Labels = raw19119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19119 raw19119Labels permutation590 hz
    mixedMoment B raw19119step0 raw19119step0Labels = mixedMoment B raw19119step1 raw19119step1Labels := by
      have ha : raw19119step1 = (fun i j => raw19119step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19119step1 raw19119step0; decide +kernel
      have hl : raw19119step1Labels = raw19119step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19119step0 raw19119step0Labels permutation56 permutation7
    mixedMoment B raw19119step1 raw19119step1Labels = mixedMoment B raw19119step2 raw19119step2Labels := by
      have ha : raw19119step2 = -raw19119step1 := by apply Matrix.ext; change ∀ i j, raw19119step2 i j = -(raw19119step1 i j); unfold raw19119step2 raw19119step1; decide +kernel
      have hl : raw19119step2Labels = raw19119step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19119step2 raw19119step2Labels = mixedMoment B raw19119step3 raw19119step3Labels := by
      have ha : raw19119step3 = raw19119step2 := by apply Matrix.ext; unfold raw19119step3 raw19119step2; decide +kernel
      have hl : raw19119step2Labels = labelEmbedding1 ∘ raw19119step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19119step2 raw19119step2Labels raw19119step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw19120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw19120step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19120step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw19120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19120step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw19120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19120 raw19120Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw19120 raw19120Labels = mixedMoment B raw19120step0 raw19120step0Labels := by
      have ha : raw19120step0 = (fun i j => raw19120 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19120step0 raw19120; decide +kernel
      have hl : raw19120step0Labels = raw19120Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19120 raw19120Labels permutation184 permutation5
    mixedMoment B raw19120step0 raw19120step0Labels = mixedMoment B raw19120step1 raw19120step1Labels := by
      have ha : raw19120step1 = -raw19120step0 := by apply Matrix.ext; change ∀ i j, raw19120step1 i j = -(raw19120step0 i j); unfold raw19120step1 raw19120step0; decide +kernel
      have hl : raw19120step1Labels = raw19120step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19120step1 raw19120step1Labels = mixedMoment B raw19120step2 raw19120step2Labels := by
      have ha : raw19120step2 = raw19120step1 := by apply Matrix.ext; unfold raw19120step2 raw19120step1; decide +kernel
      have hl : raw19120step1Labels = labelEmbedding1 ∘ raw19120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19120step1 raw19120step1Labels raw19120step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

def raw19121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19121step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19121step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19121step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19121 raw19121Labels = mixedMoment B node3765 node3765Labels := by
  calc
    mixedMoment B raw19121 raw19121Labels = mixedMoment B raw19121step0 raw19121step0Labels := by
      have ha : raw19121step0 = (fun i j => raw19121 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19121step0 raw19121; decide +kernel
      have hl : raw19121step0Labels = raw19121Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19121 raw19121Labels permutation283 permutation7
    mixedMoment B raw19121step0 raw19121step0Labels = mixedMoment B raw19121step1 raw19121step1Labels := by
      have ha : raw19121step1 = -raw19121step0 := by apply Matrix.ext; change ∀ i j, raw19121step1 i j = -(raw19121step0 i j); unfold raw19121step1 raw19121step0; decide +kernel
      have hl : raw19121step1Labels = raw19121step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19121step1 raw19121step1Labels = mixedMoment B raw19121step2 raw19121step2Labels := by
      have ha : raw19121step2 = raw19121step1 := by apply Matrix.ext; unfold raw19121step2 raw19121step1; decide +kernel
      have hl : raw19121step1Labels = labelEmbedding1 ∘ raw19121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19121step1 raw19121step1Labels raw19121step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3765 node3765Labels := by rfl

def raw19122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19122step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19122step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19122step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19122 raw19122Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw19122 raw19122Labels = mixedMoment B raw19122step0 raw19122step0Labels := by
      have ha : raw19122step0 = (fun i j => raw19122 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19122step0 raw19122; decide +kernel
      have hl : raw19122step0Labels = raw19122Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19122 raw19122Labels permutation285 permutation7
    mixedMoment B raw19122step0 raw19122step0Labels = mixedMoment B raw19122step1 raw19122step1Labels := by
      have ha : raw19122step1 = -raw19122step0 := by apply Matrix.ext; change ∀ i j, raw19122step1 i j = -(raw19122step0 i j); unfold raw19122step1 raw19122step0; decide +kernel
      have hl : raw19122step1Labels = raw19122step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19122step1 raw19122step1Labels = mixedMoment B raw19122step2 raw19122step2Labels := by
      have ha : raw19122step2 = raw19122step1 := by apply Matrix.ext; unfold raw19122step2 raw19122step1; decide +kernel
      have hl : raw19122step1Labels = labelEmbedding1 ∘ raw19122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19122step1 raw19122step1Labels raw19122step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw19123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19123Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19123step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19123step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19123 raw19123Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw19123 raw19123Labels = mixedMoment B raw19123step0 raw19123step0Labels := by
      have ha : raw19123step0 = (fun i j => raw19123 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19123step0 raw19123; decide +kernel
      have hl : raw19123step0Labels = raw19123Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19123 raw19123Labels permutation287 permutation7
    mixedMoment B raw19123step0 raw19123step0Labels = mixedMoment B raw19123step1 raw19123step1Labels := by
      have ha : raw19123step1 = -raw19123step0 := by apply Matrix.ext; change ∀ i j, raw19123step1 i j = -(raw19123step0 i j); unfold raw19123step1 raw19123step0; decide +kernel
      have hl : raw19123step1Labels = raw19123step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19123step1 raw19123step1Labels = mixedMoment B raw19123step2 raw19123step2Labels := by
      have ha : raw19123step2 = raw19123step1 := by apply Matrix.ext; unfold raw19123step2 raw19123step1; decide +kernel
      have hl : raw19123step1Labels = labelEmbedding1 ∘ raw19123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19123step1 raw19123step1Labels raw19123step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw19124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19124step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19124step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19124step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19124step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19124step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19124 raw19124Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw19124 raw19124Labels = mixedMoment B raw19124step0 raw19124step0Labels := by
      have hz : ∀ j, raw19124 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19124step0 = (fun i j => raw19124 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19124step0 raw19124; decide +kernel
      have hl : raw19124step0Labels = raw19124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19124 raw19124Labels permutation590 hz
    mixedMoment B raw19124step0 raw19124step0Labels = mixedMoment B raw19124step1 raw19124step1Labels := by
      have ha : raw19124step1 = (fun i j => raw19124step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19124step1 raw19124step0; decide +kernel
      have hl : raw19124step1Labels = raw19124step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19124step0 raw19124step0Labels permutation56 permutation7
    mixedMoment B raw19124step1 raw19124step1Labels = mixedMoment B raw19124step2 raw19124step2Labels := by
      have ha : raw19124step2 = -raw19124step1 := by apply Matrix.ext; change ∀ i j, raw19124step2 i j = -(raw19124step1 i j); unfold raw19124step2 raw19124step1; decide +kernel
      have hl : raw19124step2Labels = raw19124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19124step2 raw19124step2Labels = mixedMoment B raw19124step3 raw19124step3Labels := by
      have ha : raw19124step3 = raw19124step2 := by apply Matrix.ext; unfold raw19124step3 raw19124step2; decide +kernel
      have hl : raw19124step2Labels = labelEmbedding1 ∘ raw19124step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19124step2 raw19124step2Labels raw19124step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3962 node3962Labels := by rfl

def raw19125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19125Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19125step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19125step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19125step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19125 raw19125Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw19125 raw19125Labels = mixedMoment B raw19125step0 raw19125step0Labels := by
      have ha : raw19125step0 = (fun i j => raw19125 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19125step0 raw19125; decide +kernel
      have hl : raw19125step0Labels = raw19125Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19125 raw19125Labels permutation189 permutation5
    mixedMoment B raw19125step0 raw19125step0Labels = mixedMoment B raw19125step1 raw19125step1Labels := by
      have ha : raw19125step1 = -raw19125step0 := by apply Matrix.ext; change ∀ i j, raw19125step1 i j = -(raw19125step0 i j); unfold raw19125step1 raw19125step0; decide +kernel
      have hl : raw19125step1Labels = raw19125step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19125step1 raw19125step1Labels = mixedMoment B raw19125step2 raw19125step2Labels := by
      have ha : raw19125step2 = raw19125step1 := by apply Matrix.ext; unfold raw19125step2 raw19125step1; decide +kernel
      have hl : raw19125step1Labels = labelEmbedding1 ∘ raw19125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19125step1 raw19125step1Labels raw19125step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw19126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19126step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19126step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19126 raw19126Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw19126 raw19126Labels = mixedMoment B raw19126step0 raw19126step0Labels := by
      have ha : raw19126step0 = (fun i j => raw19126 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19126step0 raw19126; decide +kernel
      have hl : raw19126step0Labels = raw19126Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19126 raw19126Labels permutation284 permutation7
    mixedMoment B raw19126step0 raw19126step0Labels = mixedMoment B raw19126step1 raw19126step1Labels := by
      have ha : raw19126step1 = -raw19126step0 := by apply Matrix.ext; change ∀ i j, raw19126step1 i j = -(raw19126step0 i j); unfold raw19126step1 raw19126step0; decide +kernel
      have hl : raw19126step1Labels = raw19126step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19126step1 raw19126step1Labels = mixedMoment B raw19126step2 raw19126step2Labels := by
      have ha : raw19126step2 = raw19126step1 := by apply Matrix.ext; unfold raw19126step2 raw19126step1; decide +kernel
      have hl : raw19126step1Labels = labelEmbedding1 ∘ raw19126step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19126step1 raw19126step1Labels raw19126step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw19127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19127Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19127step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19127step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19127 raw19127Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw19127 raw19127Labels = mixedMoment B raw19127step0 raw19127step0Labels := by
      have ha : raw19127step0 = (fun i j => raw19127 (permutation357 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19127step0 raw19127; decide +kernel
      have hl : raw19127step0Labels = raw19127Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19127 raw19127Labels permutation357 permutation5
    mixedMoment B raw19127step0 raw19127step0Labels = mixedMoment B raw19127step1 raw19127step1Labels := by
      have ha : raw19127step1 = -raw19127step0 := by apply Matrix.ext; change ∀ i j, raw19127step1 i j = -(raw19127step0 i j); unfold raw19127step1 raw19127step0; decide +kernel
      have hl : raw19127step1Labels = raw19127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19127step1 raw19127step1Labels = mixedMoment B raw19127step2 raw19127step2Labels := by
      have ha : raw19127step2 = raw19127step1 := by apply Matrix.ext; unfold raw19127step2 raw19127step1; decide +kernel
      have hl : raw19127step1Labels = labelEmbedding1 ∘ raw19127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19127step1 raw19127step1Labels raw19127step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw19128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19128step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19128step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19128 raw19128Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw19128 raw19128Labels = mixedMoment B raw19128step0 raw19128step0Labels := by
      have ha : raw19128step0 = (fun i j => raw19128 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19128step0 raw19128; decide +kernel
      have hl : raw19128step0Labels = raw19128Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19128 raw19128Labels permutation284 permutation7
    mixedMoment B raw19128step0 raw19128step0Labels = mixedMoment B raw19128step1 raw19128step1Labels := by
      have ha : raw19128step1 = -raw19128step0 := by apply Matrix.ext; change ∀ i j, raw19128step1 i j = -(raw19128step0 i j); unfold raw19128step1 raw19128step0; decide +kernel
      have hl : raw19128step1Labels = raw19128step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19128step1 raw19128step1Labels = mixedMoment B raw19128step2 raw19128step2Labels := by
      have ha : raw19128step2 = raw19128step1 := by apply Matrix.ext; unfold raw19128step2 raw19128step1; decide +kernel
      have hl : raw19128step1Labels = labelEmbedding1 ∘ raw19128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19128step1 raw19128step1Labels raw19128step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw19129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw19129step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19129step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19129step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19129step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19129 raw19129Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw19129 raw19129Labels = mixedMoment B raw19129step0 raw19129step0Labels := by
      have hz : ∀ j, raw19129 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19129step0 = (fun i j => raw19129 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19129step0 raw19129; decide +kernel
      have hl : raw19129step0Labels = raw19129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19129 raw19129Labels permutation590 hz
    mixedMoment B raw19129step0 raw19129step0Labels = mixedMoment B raw19129step1 raw19129step1Labels := by
      have ha : raw19129step1 = (fun i j => raw19129step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19129step1 raw19129step0; decide +kernel
      have hl : raw19129step1Labels = raw19129step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19129step0 raw19129step0Labels permutation57 permutation7
    mixedMoment B raw19129step1 raw19129step1Labels = mixedMoment B raw19129step2 raw19129step2Labels := by
      have ha : raw19129step2 = -raw19129step1 := by apply Matrix.ext; change ∀ i j, raw19129step2 i j = -(raw19129step1 i j); unfold raw19129step2 raw19129step1; decide +kernel
      have hl : raw19129step2Labels = raw19129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19129step2 raw19129step2Labels = mixedMoment B raw19129step3 raw19129step3Labels := by
      have ha : raw19129step3 = raw19129step2 := by apply Matrix.ext; unfold raw19129step3 raw19129step2; decide +kernel
      have hl : raw19129step2Labels = labelEmbedding1 ∘ raw19129step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19129step2 raw19129step2Labels raw19129step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw19130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19130step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19130step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19130 raw19130Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw19130 raw19130Labels = mixedMoment B raw19130step0 raw19130step0Labels := by
      have ha : raw19130step0 = (fun i j => raw19130 (permutation183 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19130step0 raw19130; decide +kernel
      have hl : raw19130step0Labels = raw19130Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19130 raw19130Labels permutation183 permutation5
    mixedMoment B raw19130step0 raw19130step0Labels = mixedMoment B raw19130step1 raw19130step1Labels := by
      have ha : raw19130step1 = -raw19130step0 := by apply Matrix.ext; change ∀ i j, raw19130step1 i j = -(raw19130step0 i j); unfold raw19130step1 raw19130step0; decide +kernel
      have hl : raw19130step1Labels = raw19130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19130step1 raw19130step1Labels = mixedMoment B raw19130step2 raw19130step2Labels := by
      have ha : raw19130step2 = raw19130step1 := by apply Matrix.ext; unfold raw19130step2 raw19130step1; decide +kernel
      have hl : raw19130step1Labels = labelEmbedding1 ∘ raw19130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19130step1 raw19130step1Labels raw19130step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw19131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19131step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19131step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19131step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19131step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19131 raw19131Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw19131 raw19131Labels = mixedMoment B raw19131step0 raw19131step0Labels := by
      have ha : raw19131step0 = (fun i j => raw19131 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19131step0 raw19131; decide +kernel
      have hl : raw19131step0Labels = raw19131Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19131 raw19131Labels permutation283 permutation7
    mixedMoment B raw19131step0 raw19131step0Labels = mixedMoment B raw19131step1 raw19131step1Labels := by
      have ha : raw19131step1 = -raw19131step0 := by apply Matrix.ext; change ∀ i j, raw19131step1 i j = -(raw19131step0 i j); unfold raw19131step1 raw19131step0; decide +kernel
      have hl : raw19131step1Labels = raw19131step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19131step1 raw19131step1Labels = mixedMoment B raw19131step2 raw19131step2Labels := by
      have ha : raw19131step2 = raw19131step1 := by apply Matrix.ext; unfold raw19131step2 raw19131step1; decide +kernel
      have hl : raw19131step1Labels = labelEmbedding1 ∘ raw19131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19131step1 raw19131step1Labels raw19131step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw19132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19132step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19132 raw19132Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw19132 raw19132Labels = mixedMoment B raw19132step0 raw19132step0Labels := by
      have ha : raw19132step0 = (fun i j => raw19132 (permutation353 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19132step0 raw19132; decide +kernel
      have hl : raw19132step0Labels = raw19132Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19132 raw19132Labels permutation353 permutation5
    mixedMoment B raw19132step0 raw19132step0Labels = mixedMoment B raw19132step1 raw19132step1Labels := by
      have ha : raw19132step1 = -raw19132step0 := by apply Matrix.ext; change ∀ i j, raw19132step1 i j = -(raw19132step0 i j); unfold raw19132step1 raw19132step0; decide +kernel
      have hl : raw19132step1Labels = raw19132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19132step1 raw19132step1Labels = mixedMoment B raw19132step2 raw19132step2Labels := by
      have ha : raw19132step2 = raw19132step1 := by apply Matrix.ext; unfold raw19132step2 raw19132step1; decide +kernel
      have hl : raw19132step1Labels = labelEmbedding1 ∘ raw19132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19132step1 raw19132step1Labels raw19132step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw19133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19133step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19133step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19133step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19133 raw19133Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw19133 raw19133Labels = mixedMoment B raw19133step0 raw19133step0Labels := by
      have ha : raw19133step0 = (fun i j => raw19133 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19133step0 raw19133; decide +kernel
      have hl : raw19133step0Labels = raw19133Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19133 raw19133Labels permutation283 permutation7
    mixedMoment B raw19133step0 raw19133step0Labels = mixedMoment B raw19133step1 raw19133step1Labels := by
      have ha : raw19133step1 = -raw19133step0 := by apply Matrix.ext; change ∀ i j, raw19133step1 i j = -(raw19133step0 i j); unfold raw19133step1 raw19133step0; decide +kernel
      have hl : raw19133step1Labels = raw19133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19133step1 raw19133step1Labels = mixedMoment B raw19133step2 raw19133step2Labels := by
      have ha : raw19133step2 = raw19133step1 := by apply Matrix.ext; unfold raw19133step2 raw19133step1; decide +kernel
      have hl : raw19133step1Labels = labelEmbedding1 ∘ raw19133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19133step1 raw19133step1Labels raw19133step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw19134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19134step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19134step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19134step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19134step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19134step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19134 raw19134Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw19134 raw19134Labels = mixedMoment B raw19134step0 raw19134step0Labels := by
      have hz : ∀ j, raw19134 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19134step0 = (fun i j => raw19134 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19134step0 raw19134; decide +kernel
      have hl : raw19134step0Labels = raw19134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19134 raw19134Labels permutation590 hz
    mixedMoment B raw19134step0 raw19134step0Labels = mixedMoment B raw19134step1 raw19134step1Labels := by
      have ha : raw19134step1 = (fun i j => raw19134step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19134step1 raw19134step0; decide +kernel
      have hl : raw19134step1Labels = raw19134step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19134step0 raw19134step0Labels permutation56 permutation7
    mixedMoment B raw19134step1 raw19134step1Labels = mixedMoment B raw19134step2 raw19134step2Labels := by
      have ha : raw19134step2 = -raw19134step1 := by apply Matrix.ext; change ∀ i j, raw19134step2 i j = -(raw19134step1 i j); unfold raw19134step2 raw19134step1; decide +kernel
      have hl : raw19134step2Labels = raw19134step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19134step2 raw19134step2Labels = mixedMoment B raw19134step3 raw19134step3Labels := by
      have ha : raw19134step3 = raw19134step2 := by apply Matrix.ext; unfold raw19134step3 raw19134step2; decide +kernel
      have hl : raw19134step2Labels = labelEmbedding1 ∘ raw19134step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19134step2 raw19134step2Labels raw19134step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw19135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19135step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19135step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19135step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19135 raw19135Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw19135 raw19135Labels = mixedMoment B raw19135step0 raw19135step0Labels := by
      have ha : raw19135step0 = (fun i j => raw19135 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19135step0 raw19135; decide +kernel
      have hl : raw19135step0Labels = raw19135Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19135 raw19135Labels permutation184 permutation5
    mixedMoment B raw19135step0 raw19135step0Labels = mixedMoment B raw19135step1 raw19135step1Labels := by
      have ha : raw19135step1 = -raw19135step0 := by apply Matrix.ext; change ∀ i j, raw19135step1 i j = -(raw19135step0 i j); unfold raw19135step1 raw19135step0; decide +kernel
      have hl : raw19135step1Labels = raw19135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19135step1 raw19135step1Labels = mixedMoment B raw19135step2 raw19135step2Labels := by
      have ha : raw19135step2 = raw19135step1 := by apply Matrix.ext; unfold raw19135step2 raw19135step1; decide +kernel
      have hl : raw19135step1Labels = labelEmbedding1 ∘ raw19135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19135step1 raw19135step1Labels raw19135step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

def raw19136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19136step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19136step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19136 raw19136Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw19136 raw19136Labels = mixedMoment B raw19136step0 raw19136step0Labels := by
      have ha : raw19136step0 = (fun i j => raw19136 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19136step0 raw19136; decide +kernel
      have hl : raw19136step0Labels = raw19136Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19136 raw19136Labels permutation283 permutation7
    mixedMoment B raw19136step0 raw19136step0Labels = mixedMoment B raw19136step1 raw19136step1Labels := by
      have ha : raw19136step1 = -raw19136step0 := by apply Matrix.ext; change ∀ i j, raw19136step1 i j = -(raw19136step0 i j); unfold raw19136step1 raw19136step0; decide +kernel
      have hl : raw19136step1Labels = raw19136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19136step1 raw19136step1Labels = mixedMoment B raw19136step2 raw19136step2Labels := by
      have ha : raw19136step2 = raw19136step1 := by apply Matrix.ext; unfold raw19136step2 raw19136step1; decide +kernel
      have hl : raw19136step1Labels = labelEmbedding1 ∘ raw19136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19136step1 raw19136step1Labels raw19136step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw19137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19137step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19137 raw19137Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw19137 raw19137Labels = mixedMoment B raw19137step0 raw19137step0Labels := by
      have ha : raw19137step0 = (fun i j => raw19137 (permutation615 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19137step0 raw19137; decide +kernel
      have hl : raw19137step0Labels = raw19137Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19137 raw19137Labels permutation615 permutation5
    mixedMoment B raw19137step0 raw19137step0Labels = mixedMoment B raw19137step1 raw19137step1Labels := by
      have ha : raw19137step1 = raw19137step0 := by apply Matrix.ext; unfold raw19137step1 raw19137step0; decide +kernel
      have hl : raw19137step0Labels = labelEmbedding1 ∘ raw19137step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19137step0 raw19137step0Labels raw19137step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw19138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19138step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19138 raw19138Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw19138 raw19138Labels = mixedMoment B raw19138step0 raw19138step0Labels := by
      have ha : raw19138step0 = (fun i j => raw19138 (permutation620 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19138step0 raw19138; decide +kernel
      have hl : raw19138step0Labels = raw19138Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19138 raw19138Labels permutation620 permutation5
    mixedMoment B raw19138step0 raw19138step0Labels = mixedMoment B raw19138step1 raw19138step1Labels := by
      have ha : raw19138step1 = raw19138step0 := by apply Matrix.ext; unfold raw19138step1 raw19138step0; decide +kernel
      have hl : raw19138step0Labels = labelEmbedding1 ∘ raw19138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19138step0 raw19138step0Labels raw19138step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw19139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19139step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19139 raw19139Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw19139 raw19139Labels = mixedMoment B raw19139step0 raw19139step0Labels := by
      have ha : raw19139step0 = (fun i j => raw19139 (permutation614 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19139step0 raw19139; decide +kernel
      have hl : raw19139step0Labels = raw19139Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19139 raw19139Labels permutation614 permutation5
    mixedMoment B raw19139step0 raw19139step0Labels = mixedMoment B raw19139step1 raw19139step1Labels := by
      have ha : raw19139step1 = raw19139step0 := by apply Matrix.ext; unfold raw19139step1 raw19139step0; decide +kernel
      have hl : raw19139step0Labels = labelEmbedding1 ∘ raw19139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19139step0 raw19139step0Labels raw19139step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw19140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19140step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19140step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19140step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19140 raw19140Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw19140 raw19140Labels = mixedMoment B raw19140step0 raw19140step0Labels := by
      have ha : raw19140step0 = (fun i j => raw19140 (permutation283 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19140step0 raw19140; decide +kernel
      have hl : raw19140step0Labels = raw19140Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19140 raw19140Labels permutation283 permutation5
    mixedMoment B raw19140step0 raw19140step0Labels = mixedMoment B raw19140step1 raw19140step1Labels := by
      have ha : raw19140step1 = -raw19140step0 := by apply Matrix.ext; change ∀ i j, raw19140step1 i j = -(raw19140step0 i j); unfold raw19140step1 raw19140step0; decide +kernel
      have hl : raw19140step1Labels = raw19140step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19140step1 raw19140step1Labels = mixedMoment B raw19140step2 raw19140step2Labels := by
      have ha : raw19140step2 = raw19140step1 := by apply Matrix.ext; unfold raw19140step2 raw19140step1; decide +kernel
      have hl : raw19140step1Labels = labelEmbedding8 ∘ raw19140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19140step1 raw19140step1Labels raw19140step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw19141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19141step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19141step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19141 raw19141Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw19141 raw19141Labels = mixedMoment B raw19141step0 raw19141step0Labels := by
      have ha : raw19141step0 = (fun i j => raw19141 (permutation269 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19141step0 raw19141; decide +kernel
      have hl : raw19141step0Labels = raw19141Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19141 raw19141Labels permutation269 permutation5
    mixedMoment B raw19141step0 raw19141step0Labels = mixedMoment B raw19141step1 raw19141step1Labels := by
      have ha : raw19141step1 = -raw19141step0 := by apply Matrix.ext; change ∀ i j, raw19141step1 i j = -(raw19141step0 i j); unfold raw19141step1 raw19141step0; decide +kernel
      have hl : raw19141step1Labels = raw19141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19141step1 raw19141step1Labels = mixedMoment B raw19141step2 raw19141step2Labels := by
      have ha : raw19141step2 = raw19141step1 := by apply Matrix.ext; unfold raw19141step2 raw19141step1; decide +kernel
      have hl : raw19141step1Labels = labelEmbedding8 ∘ raw19141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19141step1 raw19141step1Labels raw19141step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw19142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19142step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19142step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19142step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19142 raw19142Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19142 raw19142Labels = mixedMoment B raw19142step0 raw19142step0Labels := by
      have hz : ∀ j, raw19142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19142step0 = (fun i j => raw19142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19142step0 raw19142; decide +kernel
      have hl : raw19142step0Labels = raw19142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19142 raw19142Labels permutation434 hz
    mixedMoment B raw19142step0 raw19142step0Labels = mixedMoment B raw19142step1 raw19142step1Labels := by
      have ha : raw19142step1 = (fun i j => raw19142step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19142step1 raw19142step0; decide +kernel
      have hl : raw19142step1Labels = raw19142step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19142step0 raw19142step0Labels permutation75 permutation4
    mixedMoment B raw19142step1 raw19142step1Labels = mixedMoment B raw19142step2 raw19142step2Labels := by
      have ha : raw19142step2 = -raw19142step1 := by apply Matrix.ext; change ∀ i j, raw19142step2 i j = -(raw19142step1 i j); unfold raw19142step2 raw19142step1; decide +kernel
      have hl : raw19142step2Labels = raw19142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19142step2 raw19142step2Labels = mixedMoment B raw19142step3 raw19142step3Labels := by
      have ha : raw19142step3 = raw19142step2 := by apply Matrix.ext; unfold raw19142step3 raw19142step2; decide +kernel
      have hl : raw19142step2Labels = labelEmbedding7 ∘ raw19142step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19142step2 raw19142step2Labels raw19142step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw19143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19143step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19143step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19143step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19143step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19143 raw19143Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19143 raw19143Labels = mixedMoment B raw19143step0 raw19143step0Labels := by
      have hz : ∀ j, raw19143 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19143step0 = (fun i j => raw19143 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19143step0 raw19143; decide +kernel
      have hl : raw19143step0Labels = raw19143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19143 raw19143Labels permutation520 hz
    mixedMoment B raw19143step0 raw19143step0Labels = mixedMoment B raw19143step1 raw19143step1Labels := by
      have ha : raw19143step1 = (fun i j => raw19143step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19143step1 raw19143step0; decide +kernel
      have hl : raw19143step1Labels = raw19143step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19143step0 raw19143step0Labels permutation75 permutation4
    mixedMoment B raw19143step1 raw19143step1Labels = mixedMoment B raw19143step2 raw19143step2Labels := by
      have ha : raw19143step2 = -raw19143step1 := by apply Matrix.ext; change ∀ i j, raw19143step2 i j = -(raw19143step1 i j); unfold raw19143step2 raw19143step1; decide +kernel
      have hl : raw19143step2Labels = raw19143step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19143step2 raw19143step2Labels = mixedMoment B raw19143step3 raw19143step3Labels := by
      have ha : raw19143step3 = raw19143step2 := by apply Matrix.ext; unfold raw19143step3 raw19143step2; decide +kernel
      have hl : raw19143step2Labels = labelEmbedding7 ∘ raw19143step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19143step2 raw19143step2Labels raw19143step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw19144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19144step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19144step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19144 raw19144Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19144 raw19144Labels = mixedMoment B raw19144step0 raw19144step0Labels := by
      have ha : raw19144step0 = (fun i j => raw19144 (permutation336 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19144step0 raw19144; decide +kernel
      have hl : raw19144step0Labels = raw19144Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19144 raw19144Labels permutation336 permutation4
    mixedMoment B raw19144step0 raw19144step0Labels = mixedMoment B raw19144step1 raw19144step1Labels := by
      have ha : raw19144step1 = -raw19144step0 := by apply Matrix.ext; change ∀ i j, raw19144step1 i j = -(raw19144step0 i j); unfold raw19144step1 raw19144step0; decide +kernel
      have hl : raw19144step1Labels = raw19144step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19144step1 raw19144step1Labels = mixedMoment B raw19144step2 raw19144step2Labels := by
      have ha : raw19144step2 = raw19144step1 := by apply Matrix.ext; unfold raw19144step2 raw19144step1; decide +kernel
      have hl : raw19144step1Labels = labelEmbedding7 ∘ raw19144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19144step1 raw19144step1Labels raw19144step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19145step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19145 raw19145Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw19145 raw19145Labels = mixedMoment B raw19145step0 raw19145step0Labels := by
      have ha : raw19145step0 = (fun i j => raw19145 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19145step0 raw19145; decide +kernel
      have hl : raw19145step0Labels = raw19145Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19145 raw19145Labels permutation156 permutation3
    mixedMoment B raw19145step0 raw19145step0Labels = mixedMoment B raw19145step1 raw19145step1Labels := by
      have ha : raw19145step1 = raw19145step0 := by apply Matrix.ext; unfold raw19145step1 raw19145step0; decide +kernel
      have hl : raw19145step0Labels = labelEmbedding6 ∘ raw19145step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19145step0 raw19145step0Labels raw19145step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw19146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19146 raw19146Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19146 raw19146Labels = mixedMoment B raw19146step0 raw19146step0Labels := by
      have ha : raw19146step0 = (fun i j => raw19146 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19146step0 raw19146; decide +kernel
      have hl : raw19146step0Labels = raw19146Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19146 raw19146Labels permutation176 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19147 raw19147Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19147 raw19147Labels = mixedMoment B raw19147step0 raw19147step0Labels := by
      have hz : ∀ j, raw19147 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19147step0 = (fun i j => raw19147 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19147step0 raw19147; decide +kernel
      have hl : raw19147step0Labels = raw19147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19147 raw19147Labels permutation434 hz
    mixedMoment B raw19147step0 raw19147step0Labels = mixedMoment B raw19147step1 raw19147step1Labels := by
      have ha : raw19147step1 = (fun i j => raw19147step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19147step1 raw19147step0; decide +kernel
      have hl : raw19147step1Labels = raw19147step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19147step0 raw19147step0Labels permutation38 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw19148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19148 raw19148Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19148 raw19148Labels = mixedMoment B raw19148step0 raw19148step0Labels := by
      have hz : ∀ j, raw19148 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19148step0 = (fun i j => raw19148 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19148step0 raw19148; decide +kernel
      have hl : raw19148step0Labels = raw19148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19148 raw19148Labels permutation520 hz
    mixedMoment B raw19148step0 raw19148step0Labels = mixedMoment B raw19148step1 raw19148step1Labels := by
      have ha : raw19148step1 = (fun i j => raw19148step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19148step1 raw19148step0; decide +kernel
      have hl : raw19148step1Labels = raw19148step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19148step0 raw19148step0Labels permutation38 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw19149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19149step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19149 raw19149Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw19149 raw19149Labels = mixedMoment B raw19149step0 raw19149step0Labels := by
      have ha : raw19149step0 = (fun i j => raw19149 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19149step0 raw19149; decide +kernel
      have hl : raw19149step0Labels = raw19149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19149 raw19149Labels permutation170 permutation3
    mixedMoment B raw19149step0 raw19149step0Labels = mixedMoment B raw19149step1 raw19149step1Labels := by
      have ha : raw19149step1 = raw19149step0 := by apply Matrix.ext; unfold raw19149step1 raw19149step0; decide +kernel
      have hl : raw19149step0Labels = labelEmbedding6 ∘ raw19149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19149step0 raw19149step0Labels raw19149step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw19150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19150step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19150step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19150 raw19150Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw19150 raw19150Labels = mixedMoment B raw19150step0 raw19150step0Labels := by
      have ha : raw19150step0 = (fun i j => raw19150 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19150step0 raw19150; decide +kernel
      have hl : raw19150step0Labels = raw19150Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19150 raw19150Labels permutation173 permutation3
    mixedMoment B raw19150step0 raw19150step0Labels = mixedMoment B raw19150step1 raw19150step1Labels := by
      have ha : raw19150step1 = raw19150step0 := by apply Matrix.ext; unfold raw19150step1 raw19150step0; decide +kernel
      have hl : raw19150step0Labels = labelEmbedding6 ∘ raw19150step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19150step0 raw19150step0Labels raw19150step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw19151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19151step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19151step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19151step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19151step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19151 raw19151Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw19151 raw19151Labels = mixedMoment B raw19151step0 raw19151step0Labels := by
      have ha : raw19151step0 = (fun i j => raw19151 (permutation286 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19151step0 raw19151; decide +kernel
      have hl : raw19151step0Labels = raw19151Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19151 raw19151Labels permutation286 permutation5
    mixedMoment B raw19151step0 raw19151step0Labels = mixedMoment B raw19151step1 raw19151step1Labels := by
      have ha : raw19151step1 = -raw19151step0 := by apply Matrix.ext; change ∀ i j, raw19151step1 i j = -(raw19151step0 i j); unfold raw19151step1 raw19151step0; decide +kernel
      have hl : raw19151step1Labels = raw19151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19151step1 raw19151step1Labels = mixedMoment B raw19151step2 raw19151step2Labels := by
      have ha : raw19151step2 = raw19151step1 := by apply Matrix.ext; unfold raw19151step2 raw19151step1; decide +kernel
      have hl : raw19151step1Labels = labelEmbedding8 ∘ raw19151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19151step1 raw19151step1Labels raw19151step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

def raw19152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19152step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19152step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19152step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19152step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19152 raw19152Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw19152 raw19152Labels = mixedMoment B raw19152step0 raw19152step0Labels := by
      have hz : ∀ j, raw19152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19152step0 = (fun i j => raw19152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19152step0 raw19152; decide +kernel
      have hl : raw19152step0Labels = raw19152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19152 raw19152Labels permutation434 hz
    mixedMoment B raw19152step0 raw19152step0Labels = mixedMoment B raw19152step1 raw19152step1Labels := by
      have ha : raw19152step1 = (fun i j => raw19152step0 (permutation61 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19152step1 raw19152step0; decide +kernel
      have hl : raw19152step1Labels = raw19152step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19152step0 raw19152step0Labels permutation61 permutation5
    mixedMoment B raw19152step1 raw19152step1Labels = mixedMoment B raw19152step2 raw19152step2Labels := by
      have ha : raw19152step2 = -raw19152step1 := by apply Matrix.ext; change ∀ i j, raw19152step2 i j = -(raw19152step1 i j); unfold raw19152step2 raw19152step1; decide +kernel
      have hl : raw19152step2Labels = raw19152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19152step2 raw19152step2Labels = mixedMoment B raw19152step3 raw19152step3Labels := by
      have ha : raw19152step3 = raw19152step2 := by apply Matrix.ext; unfold raw19152step3 raw19152step2; decide +kernel
      have hl : raw19152step2Labels = labelEmbedding8 ∘ raw19152step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19152step2 raw19152step2Labels raw19152step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw19153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19153step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19153step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19153step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19153step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19153 raw19153Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw19153 raw19153Labels = mixedMoment B raw19153step0 raw19153step0Labels := by
      have hz : ∀ j, raw19153 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19153step0 = (fun i j => raw19153 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19153step0 raw19153; decide +kernel
      have hl : raw19153step0Labels = raw19153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19153 raw19153Labels permutation520 hz
    mixedMoment B raw19153step0 raw19153step0Labels = mixedMoment B raw19153step1 raw19153step1Labels := by
      have ha : raw19153step1 = (fun i j => raw19153step0 (permutation61 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19153step1 raw19153step0; decide +kernel
      have hl : raw19153step1Labels = raw19153step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19153step0 raw19153step0Labels permutation61 permutation5
    mixedMoment B raw19153step1 raw19153step1Labels = mixedMoment B raw19153step2 raw19153step2Labels := by
      have ha : raw19153step2 = -raw19153step1 := by apply Matrix.ext; change ∀ i j, raw19153step2 i j = -(raw19153step1 i j); unfold raw19153step2 raw19153step1; decide +kernel
      have hl : raw19153step2Labels = raw19153step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19153step2 raw19153step2Labels = mixedMoment B raw19153step3 raw19153step3Labels := by
      have ha : raw19153step3 = raw19153step2 := by apply Matrix.ext; unfold raw19153step3 raw19153step2; decide +kernel
      have hl : raw19153step2Labels = labelEmbedding8 ∘ raw19153step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19153step2 raw19153step2Labels raw19153step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw19154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19154step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19154step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19154step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19154 raw19154Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw19154 raw19154Labels = mixedMoment B raw19154step0 raw19154step0Labels := by
      have ha : raw19154step0 = (fun i j => raw19154 (permutation286 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19154step0 raw19154; decide +kernel
      have hl : raw19154step0Labels = raw19154Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19154 raw19154Labels permutation286 permutation5
    mixedMoment B raw19154step0 raw19154step0Labels = mixedMoment B raw19154step1 raw19154step1Labels := by
      have ha : raw19154step1 = -raw19154step0 := by apply Matrix.ext; change ∀ i j, raw19154step1 i j = -(raw19154step0 i j); unfold raw19154step1 raw19154step0; decide +kernel
      have hl : raw19154step1Labels = raw19154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19154step1 raw19154step1Labels = mixedMoment B raw19154step2 raw19154step2Labels := by
      have ha : raw19154step2 = raw19154step1 := by apply Matrix.ext; unfold raw19154step2 raw19154step1; decide +kernel
      have hl : raw19154step1Labels = labelEmbedding8 ∘ raw19154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19154step1 raw19154step1Labels raw19154step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw19155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19155step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19155 raw19155Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw19155 raw19155Labels = mixedMoment B raw19155step0 raw19155step0Labels := by
      have ha : raw19155step0 = (fun i j => raw19155 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19155step0 raw19155; decide +kernel
      have hl : raw19155step0Labels = raw19155Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19155 raw19155Labels permutation157 permutation3
    mixedMoment B raw19155step0 raw19155step0Labels = mixedMoment B raw19155step1 raw19155step1Labels := by
      have ha : raw19155step1 = raw19155step0 := by apply Matrix.ext; unfold raw19155step1 raw19155step0; decide +kernel
      have hl : raw19155step0Labels = labelEmbedding6 ∘ raw19155step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19155step0 raw19155step0Labels raw19155step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw19156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw19156step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19156step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19156step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19156step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19156 raw19156Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw19156 raw19156Labels = mixedMoment B raw19156step0 raw19156step0Labels := by
      have ha : raw19156step0 = (fun i j => raw19156 (permutation284 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19156step0 raw19156; decide +kernel
      have hl : raw19156step0Labels = raw19156Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19156 raw19156Labels permutation284 permutation5
    mixedMoment B raw19156step0 raw19156step0Labels = mixedMoment B raw19156step1 raw19156step1Labels := by
      have ha : raw19156step1 = -raw19156step0 := by apply Matrix.ext; change ∀ i j, raw19156step1 i j = -(raw19156step0 i j); unfold raw19156step1 raw19156step0; decide +kernel
      have hl : raw19156step1Labels = raw19156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19156step1 raw19156step1Labels = mixedMoment B raw19156step2 raw19156step2Labels := by
      have ha : raw19156step2 = raw19156step1 := by apply Matrix.ext; unfold raw19156step2 raw19156step1; decide +kernel
      have hl : raw19156step1Labels = labelEmbedding8 ∘ raw19156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19156step1 raw19156step1Labels raw19156step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw19157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw19157step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19157step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19157step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19157 raw19157Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw19157 raw19157Labels = mixedMoment B raw19157step0 raw19157step0Labels := by
      have ha : raw19157step0 = (fun i j => raw19157 (permutation504 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19157step0 raw19157; decide +kernel
      have hl : raw19157step0Labels = raw19157Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19157 raw19157Labels permutation504 permutation3
    mixedMoment B raw19157step0 raw19157step0Labels = mixedMoment B raw19157step1 raw19157step1Labels := by
      have ha : raw19157step1 = -raw19157step0 := by apply Matrix.ext; change ∀ i j, raw19157step1 i j = -(raw19157step0 i j); unfold raw19157step1 raw19157step0; decide +kernel
      have hl : raw19157step1Labels = raw19157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19157step1 raw19157step1Labels = mixedMoment B raw19157step2 raw19157step2Labels := by
      have ha : raw19157step2 = raw19157step1 := by apply Matrix.ext; unfold raw19157step2 raw19157step1; decide +kernel
      have hl : raw19157step1Labels = labelEmbedding6 ∘ raw19157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19157step1 raw19157step1Labels raw19157step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw19158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw19158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw19158step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19158step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19158step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19158step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19158 raw19158Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw19158 raw19158Labels = mixedMoment B raw19158step0 raw19158step0Labels := by
      have hz : ∀ j, raw19158 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19158step0 = (fun i j => raw19158 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19158step0 raw19158; decide +kernel
      have hl : raw19158step0Labels = raw19158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19158 raw19158Labels permutation520 hz
    mixedMoment B raw19158step0 raw19158step0Labels = mixedMoment B raw19158step1 raw19158step1Labels := by
      have ha : raw19158step1 = (fun i j => raw19158step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19158step1 raw19158step0; decide +kernel
      have hl : raw19158step1Labels = raw19158step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19158step0 raw19158step0Labels permutation127 permutation3
    mixedMoment B raw19158step1 raw19158step1Labels = mixedMoment B raw19158step2 raw19158step2Labels := by
      have ha : raw19158step2 = -raw19158step1 := by apply Matrix.ext; change ∀ i j, raw19158step2 i j = -(raw19158step1 i j); unfold raw19158step2 raw19158step1; decide +kernel
      have hl : raw19158step2Labels = raw19158step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19158step2 raw19158step2Labels = mixedMoment B raw19158step3 raw19158step3Labels := by
      have ha : raw19158step3 = raw19158step2 := by apply Matrix.ext; unfold raw19158step3 raw19158step2; decide +kernel
      have hl : raw19158step2Labels = labelEmbedding6 ∘ raw19158step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19158step2 raw19158step2Labels raw19158step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw19159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19159step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19159 raw19159Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw19159 raw19159Labels = mixedMoment B raw19159step0 raw19159step0Labels := by
      have ha : raw19159step0 = (fun i j => raw19159 (permutation497 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19159step0 raw19159; decide +kernel
      have hl : raw19159step0Labels = raw19159Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19159 raw19159Labels permutation497 permutation5
    mixedMoment B raw19159step0 raw19159step0Labels = mixedMoment B raw19159step1 raw19159step1Labels := by
      have ha : raw19159step1 = raw19159step0 := by apply Matrix.ext; unfold raw19159step1 raw19159step0; decide +kernel
      have hl : raw19159step0Labels = labelEmbedding8 ∘ raw19159step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19159step0 raw19159step0Labels raw19159step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw19160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19160step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19160 raw19160Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw19160 raw19160Labels = mixedMoment B raw19160step0 raw19160step0Labels := by
      have ha : raw19160step0 = (fun i j => raw19160 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19160step0 raw19160; decide +kernel
      have hl : raw19160step0Labels = raw19160Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19160 raw19160Labels permutation156 permutation3
    mixedMoment B raw19160step0 raw19160step0Labels = mixedMoment B raw19160step1 raw19160step1Labels := by
      have ha : raw19160step1 = raw19160step0 := by apply Matrix.ext; unfold raw19160step1 raw19160step0; decide +kernel
      have hl : raw19160step0Labels = labelEmbedding6 ∘ raw19160step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19160step0 raw19160step0Labels raw19160step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw19161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw19161step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19161step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19161step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19161step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19161 raw19161Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw19161 raw19161Labels = mixedMoment B raw19161step0 raw19161step0Labels := by
      have ha : raw19161step0 = (fun i j => raw19161 (permutation283 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19161step0 raw19161; decide +kernel
      have hl : raw19161step0Labels = raw19161Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19161 raw19161Labels permutation283 permutation5
    mixedMoment B raw19161step0 raw19161step0Labels = mixedMoment B raw19161step1 raw19161step1Labels := by
      have ha : raw19161step1 = -raw19161step0 := by apply Matrix.ext; change ∀ i j, raw19161step1 i j = -(raw19161step0 i j); unfold raw19161step1 raw19161step0; decide +kernel
      have hl : raw19161step1Labels = raw19161step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19161step1 raw19161step1Labels = mixedMoment B raw19161step2 raw19161step2Labels := by
      have ha : raw19161step2 = raw19161step1 := by apply Matrix.ext; unfold raw19161step2 raw19161step1; decide +kernel
      have hl : raw19161step1Labels = labelEmbedding8 ∘ raw19161step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19161step1 raw19161step1Labels raw19161step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw19162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw19162step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19162step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19162step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19162step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19162 raw19162Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw19162 raw19162Labels = mixedMoment B raw19162step0 raw19162step0Labels := by
      have ha : raw19162step0 = (fun i j => raw19162 (permutation568 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19162step0 raw19162; decide +kernel
      have hl : raw19162step0Labels = raw19162Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19162 raw19162Labels permutation568 permutation3
    mixedMoment B raw19162step0 raw19162step0Labels = mixedMoment B raw19162step1 raw19162step1Labels := by
      have ha : raw19162step1 = -raw19162step0 := by apply Matrix.ext; change ∀ i j, raw19162step1 i j = -(raw19162step0 i j); unfold raw19162step1 raw19162step0; decide +kernel
      have hl : raw19162step1Labels = raw19162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19162step1 raw19162step1Labels = mixedMoment B raw19162step2 raw19162step2Labels := by
      have ha : raw19162step2 = raw19162step1 := by apply Matrix.ext; unfold raw19162step2 raw19162step1; decide +kernel
      have hl : raw19162step1Labels = labelEmbedding6 ∘ raw19162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19162step1 raw19162step1Labels raw19162step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw19163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw19163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw19163step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19163step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19163step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw19163step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19163 raw19163Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw19163 raw19163Labels = mixedMoment B raw19163step0 raw19163step0Labels := by
      have hz : ∀ j, raw19163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19163step0 = (fun i j => raw19163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19163step0 raw19163; decide +kernel
      have hl : raw19163step0Labels = raw19163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19163 raw19163Labels permutation434 hz
    mixedMoment B raw19163step0 raw19163step0Labels = mixedMoment B raw19163step1 raw19163step1Labels := by
      have ha : raw19163step1 = (fun i j => raw19163step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19163step1 raw19163step0; decide +kernel
      have hl : raw19163step1Labels = raw19163step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19163step0 raw19163step0Labels permutation127 permutation3
    mixedMoment B raw19163step1 raw19163step1Labels = mixedMoment B raw19163step2 raw19163step2Labels := by
      have ha : raw19163step2 = -raw19163step1 := by apply Matrix.ext; change ∀ i j, raw19163step2 i j = -(raw19163step1 i j); unfold raw19163step2 raw19163step1; decide +kernel
      have hl : raw19163step2Labels = raw19163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19163step2 raw19163step2Labels = mixedMoment B raw19163step3 raw19163step3Labels := by
      have ha : raw19163step3 = raw19163step2 := by apply Matrix.ext; unfold raw19163step3 raw19163step2; decide +kernel
      have hl : raw19163step2Labels = labelEmbedding6 ∘ raw19163step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19163step2 raw19163step2Labels raw19163step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw19164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw19164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19164step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19164 raw19164Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw19164 raw19164Labels = mixedMoment B raw19164step0 raw19164step0Labels := by
      have ha : raw19164step0 = (fun i j => raw19164 (permutation561 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19164step0 raw19164; decide +kernel
      have hl : raw19164step0Labels = raw19164Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19164 raw19164Labels permutation561 permutation5
    mixedMoment B raw19164step0 raw19164step0Labels = mixedMoment B raw19164step1 raw19164step1Labels := by
      have ha : raw19164step1 = raw19164step0 := by apply Matrix.ext; unfold raw19164step1 raw19164step0; decide +kernel
      have hl : raw19164step0Labels = labelEmbedding8 ∘ raw19164step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19164step0 raw19164step0Labels raw19164step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw19165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19165step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19165step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19165 raw19165Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw19165 raw19165Labels = mixedMoment B raw19165step0 raw19165step0Labels := by
      have ha : raw19165step0 = (fun i j => raw19165 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19165step0 raw19165; decide +kernel
      have hl : raw19165step0Labels = raw19165Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19165 raw19165Labels permutation152 permutation3
    mixedMoment B raw19165step0 raw19165step0Labels = mixedMoment B raw19165step1 raw19165step1Labels := by
      have ha : raw19165step1 = raw19165step0 := by apply Matrix.ext; unfold raw19165step1 raw19165step0; decide +kernel
      have hl : raw19165step0Labels = labelEmbedding6 ∘ raw19165step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19165step0 raw19165step0Labels raw19165step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

def raw19166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19166step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19166step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19166step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19166 raw19166Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw19166 raw19166Labels = mixedMoment B raw19166step0 raw19166step0Labels := by
      have ha : raw19166step0 = (fun i j => raw19166 (permutation265 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19166step0 raw19166; decide +kernel
      have hl : raw19166step0Labels = raw19166Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19166 raw19166Labels permutation265 permutation5
    mixedMoment B raw19166step0 raw19166step0Labels = mixedMoment B raw19166step1 raw19166step1Labels := by
      have ha : raw19166step1 = -raw19166step0 := by apply Matrix.ext; change ∀ i j, raw19166step1 i j = -(raw19166step0 i j); unfold raw19166step1 raw19166step0; decide +kernel
      have hl : raw19166step1Labels = raw19166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19166step1 raw19166step1Labels = mixedMoment B raw19166step2 raw19166step2Labels := by
      have ha : raw19166step2 = raw19166step1 := by apply Matrix.ext; unfold raw19166step2 raw19166step1; decide +kernel
      have hl : raw19166step1Labels = labelEmbedding8 ∘ raw19166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19166step1 raw19166step1Labels raw19166step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw19167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19167step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19167 raw19167Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw19167 raw19167Labels = mixedMoment B raw19167step0 raw19167step0Labels := by
      have ha : raw19167step0 = (fun i j => raw19167 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19167step0 raw19167; decide +kernel
      have hl : raw19167step0Labels = raw19167Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19167 raw19167Labels permutation152 permutation3
    mixedMoment B raw19167step0 raw19167step0Labels = mixedMoment B raw19167step1 raw19167step1Labels := by
      have ha : raw19167step1 = raw19167step0 := by apply Matrix.ext; unfold raw19167step1 raw19167step0; decide +kernel
      have hl : raw19167step0Labels = labelEmbedding6 ∘ raw19167step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19167step0 raw19167step0Labels raw19167step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw19168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw19168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19168step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19168step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19168 raw19168Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw19168 raw19168Labels = mixedMoment B raw19168step0 raw19168step0Labels := by
      have hz : ∀ j, raw19168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19168step0 = (fun i j => raw19168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19168step0 raw19168; decide +kernel
      have hl : raw19168step0Labels = raw19168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19168 raw19168Labels permutation434 hz
    mixedMoment B raw19168step0 raw19168step0Labels = mixedMoment B raw19168step1 raw19168step1Labels := by
      have ha : raw19168step1 = (fun i j => raw19168step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19168step1 raw19168step0; decide +kernel
      have hl : raw19168step1Labels = raw19168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19168step0 raw19168step0Labels permutation32 permutation3
    mixedMoment B raw19168step1 raw19168step1Labels = mixedMoment B raw19168step2 raw19168step2Labels := by
      have ha : raw19168step2 = raw19168step1 := by apply Matrix.ext; unfold raw19168step2 raw19168step1; decide +kernel
      have hl : raw19168step1Labels = labelEmbedding6 ∘ raw19168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19168step1 raw19168step1Labels raw19168step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw19169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw19169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw19169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19169step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19169step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19169 raw19169Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw19169 raw19169Labels = mixedMoment B raw19169step0 raw19169step0Labels := by
      have hz : ∀ j, raw19169 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19169step0 = (fun i j => raw19169 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19169step0 raw19169; decide +kernel
      have hl : raw19169step0Labels = raw19169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19169 raw19169Labels permutation520 hz
    mixedMoment B raw19169step0 raw19169step0Labels = mixedMoment B raw19169step1 raw19169step1Labels := by
      have ha : raw19169step1 = (fun i j => raw19169step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19169step1 raw19169step0; decide +kernel
      have hl : raw19169step1Labels = raw19169step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19169step0 raw19169step0Labels permutation32 permutation3
    mixedMoment B raw19169step1 raw19169step1Labels = mixedMoment B raw19169step2 raw19169step2Labels := by
      have ha : raw19169step2 = raw19169step1 := by apply Matrix.ext; unfold raw19169step2 raw19169step1; decide +kernel
      have hl : raw19169step1Labels = labelEmbedding6 ∘ raw19169step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19169step1 raw19169step1Labels raw19169step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw19170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19170step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19170step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19170 raw19170Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw19170 raw19170Labels = mixedMoment B raw19170step0 raw19170step0Labels := by
      have hz : ∀ j, raw19170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19170step0 = (fun i j => raw19170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19170step0 raw19170; decide +kernel
      have hl : raw19170step0Labels = raw19170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19170 raw19170Labels permutation346 hz
    mixedMoment B raw19170step0 raw19170step0Labels = mixedMoment B raw19170step1 raw19170step1Labels := by
      have ha : raw19170step1 = (fun i j => raw19170step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19170step1 raw19170step0; decide +kernel
      have hl : raw19170step1Labels = raw19170step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19170step0 raw19170step0Labels permutation56 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw19171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw19171step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw19171step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19171 raw19171Labels = mixedMoment B node5488 node5488Labels := by
  calc
    mixedMoment B raw19171 raw19171Labels = mixedMoment B raw19171step0 raw19171step0Labels := by
      have ha : raw19171step0 = (fun i j => raw19171 (permutation595 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19171step0 raw19171; decide +kernel
      have hl : raw19171step0Labels = raw19171Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19171 raw19171Labels permutation595 permutation6
    mixedMoment B raw19171step0 raw19171step0Labels = mixedMoment B raw19171step1 raw19171step1Labels := by
      have ha : raw19171step1 = raw19171step0 := by apply Matrix.ext; unfold raw19171step1 raw19171step0; decide +kernel
      have hl : raw19171step0Labels = labelEmbedding9 ∘ raw19171step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19171step0 raw19171step0Labels raw19171step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5488 node5488Labels := by rfl

def raw19172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2]]
def raw19172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19172step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19172step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19172step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19172 raw19172Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw19172 raw19172Labels = mixedMoment B raw19172step0 raw19172step0Labels := by
      have hz : ∀ j, raw19172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19172step0 = (fun i j => raw19172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19172step0 raw19172; decide +kernel
      have hl : raw19172step0Labels = raw19172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19172 raw19172Labels permutation434 hz
    mixedMoment B raw19172step0 raw19172step0Labels = mixedMoment B raw19172step1 raw19172step1Labels := by
      have hz : ∀ j, raw19172step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19172step1 = (fun i j => raw19172step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19172step1 raw19172step0; decide +kernel
      have hl : raw19172step1Labels = raw19172step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19172step0 raw19172step0Labels permutation80 hz
    mixedMoment B raw19172step1 raw19172step1Labels = mixedMoment B raw19172step2 raw19172step2Labels := by
      have ha : raw19172step2 = (fun i j => raw19172step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19172step2 raw19172step1; decide +kernel
      have hl : raw19172step2Labels = raw19172step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19172step1 raw19172step1Labels permutation27 permutation6
    mixedMoment B raw19172step2 raw19172step2Labels = mixedMoment B raw19172step3 raw19172step3Labels := by
      have ha : raw19172step3 = raw19172step2 := by apply Matrix.ext; unfold raw19172step3 raw19172step2; decide +kernel
      have hl : raw19172step2Labels = labelEmbedding9 ∘ raw19172step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19172step2 raw19172step2Labels raw19172step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw19173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2]]
def raw19173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19173step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19173step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19173step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19173 raw19173Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw19173 raw19173Labels = mixedMoment B raw19173step0 raw19173step0Labels := by
      have hz : ∀ j, raw19173 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19173step0 = (fun i j => raw19173 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19173step0 raw19173; decide +kernel
      have hl : raw19173step0Labels = raw19173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19173 raw19173Labels permutation520 hz
    mixedMoment B raw19173step0 raw19173step0Labels = mixedMoment B raw19173step1 raw19173step1Labels := by
      have hz : ∀ j, raw19173step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19173step1 = (fun i j => raw19173step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19173step1 raw19173step0; decide +kernel
      have hl : raw19173step1Labels = raw19173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19173step0 raw19173step0Labels permutation80 hz
    mixedMoment B raw19173step1 raw19173step1Labels = mixedMoment B raw19173step2 raw19173step2Labels := by
      have ha : raw19173step2 = (fun i j => raw19173step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19173step2 raw19173step1; decide +kernel
      have hl : raw19173step2Labels = raw19173step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19173step1 raw19173step1Labels permutation27 permutation6
    mixedMoment B raw19173step2 raw19173step2Labels = mixedMoment B raw19173step3 raw19173step3Labels := by
      have ha : raw19173step3 = raw19173step2 := by apply Matrix.ext; unfold raw19173step3 raw19173step2; decide +kernel
      have hl : raw19173step2Labels = labelEmbedding9 ∘ raw19173step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19173step2 raw19173step2Labels raw19173step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw19174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19174step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19174step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19174step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19174 raw19174Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw19174 raw19174Labels = mixedMoment B raw19174step0 raw19174step0Labels := by
      have hz : ∀ j, raw19174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19174step0 = (fun i j => raw19174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19174step0 raw19174; decide +kernel
      have hl : raw19174step0Labels = raw19174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19174 raw19174Labels permutation346 hz
    mixedMoment B raw19174step0 raw19174step0Labels = mixedMoment B raw19174step1 raw19174step1Labels := by
      have ha : raw19174step1 = (fun i j => raw19174step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19174step1 raw19174step0; decide +kernel
      have hl : raw19174step1Labels = raw19174step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19174step0 raw19174step0Labels permutation131 permutation4
    mixedMoment B raw19174step1 raw19174step1Labels = mixedMoment B raw19174step2 raw19174step2Labels := by
      have ha : raw19174step2 = -raw19174step1 := by apply Matrix.ext; change ∀ i j, raw19174step2 i j = -(raw19174step1 i j); unfold raw19174step2 raw19174step1; decide +kernel
      have hl : raw19174step2Labels = raw19174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19174step2 raw19174step2Labels = mixedMoment B raw19174step3 raw19174step3Labels := by
      have ha : raw19174step3 = raw19174step2 := by apply Matrix.ext; unfold raw19174step3 raw19174step2; decide +kernel
      have hl : raw19174step2Labels = labelEmbedding7 ∘ raw19174step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19174step2 raw19174step2Labels raw19174step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw19175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19175step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19175step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19175step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19175step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19175 raw19175Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw19175 raw19175Labels = mixedMoment B raw19175step0 raw19175step0Labels := by
      have ha : raw19175step0 = (fun i j => raw19175 (permutation197 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19175step0 raw19175; decide +kernel
      have hl : raw19175step0Labels = raw19175Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19175 raw19175Labels permutation197 permutation5
    mixedMoment B raw19175step0 raw19175step0Labels = mixedMoment B raw19175step1 raw19175step1Labels := by
      have ha : raw19175step1 = -raw19175step0 := by apply Matrix.ext; change ∀ i j, raw19175step1 i j = -(raw19175step0 i j); unfold raw19175step1 raw19175step0; decide +kernel
      have hl : raw19175step1Labels = raw19175step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19175step1 raw19175step1Labels = mixedMoment B raw19175step2 raw19175step2Labels := by
      have ha : raw19175step2 = raw19175step1 := by apply Matrix.ext; unfold raw19175step2 raw19175step1; decide +kernel
      have hl : raw19175step1Labels = labelEmbedding8 ∘ raw19175step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19175step1 raw19175step1Labels raw19175step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw19176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw19176step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw19176step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw19176step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19176 raw19176Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw19176 raw19176Labels = mixedMoment B raw19176step0 raw19176step0Labels := by
      have hz : ∀ j, raw19176 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19176step0 = (fun i j => raw19176 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19176step0 raw19176; decide +kernel
      have hl : raw19176step0Labels = raw19176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19176 raw19176Labels permutation520 hz
    mixedMoment B raw19176step0 raw19176step0Labels = mixedMoment B raw19176step1 raw19176step1Labels := by
      have hz : ∀ j, raw19176step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19176step1 = (fun i j => raw19176step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19176step1 raw19176step0; decide +kernel
      have hl : raw19176step1Labels = raw19176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19176step0 raw19176step0Labels permutation80 hz
    mixedMoment B raw19176step1 raw19176step1Labels = mixedMoment B raw19176step2 raw19176step2Labels := by
      have ha : raw19176step2 = (fun i j => raw19176step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19176step2 raw19176step1; decide +kernel
      have hl : raw19176step2Labels = raw19176step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19176step1 raw19176step1Labels permutation17 permutation4
    mixedMoment B raw19176step2 raw19176step2Labels = mixedMoment B raw19176step3 raw19176step3Labels := by
      have ha : raw19176step3 = raw19176step2 := by apply Matrix.ext; unfold raw19176step3 raw19176step2; decide +kernel
      have hl : raw19176step2Labels = labelEmbedding7 ∘ raw19176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19176step2 raw19176step2Labels raw19176step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw19177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19177step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw19177step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19177step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19177step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19177step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19177 raw19177Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw19177 raw19177Labels = mixedMoment B raw19177step0 raw19177step0Labels := by
      have hz : ∀ j, raw19177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19177step0 = (fun i j => raw19177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19177step0 raw19177; decide +kernel
      have hl : raw19177step0Labels = raw19177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19177 raw19177Labels permutation346 hz
    mixedMoment B raw19177step0 raw19177step0Labels = mixedMoment B raw19177step1 raw19177step1Labels := by
      have ha : raw19177step1 = (fun i j => raw19177step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19177step1 raw19177step0; decide +kernel
      have hl : raw19177step1Labels = raw19177step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19177step0 raw19177step0Labels permutation131 permutation4
    mixedMoment B raw19177step1 raw19177step1Labels = mixedMoment B raw19177step2 raw19177step2Labels := by
      have ha : raw19177step2 = -raw19177step1 := by apply Matrix.ext; change ∀ i j, raw19177step2 i j = -(raw19177step1 i j); unfold raw19177step2 raw19177step1; decide +kernel
      have hl : raw19177step2Labels = raw19177step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19177step2 raw19177step2Labels = mixedMoment B raw19177step3 raw19177step3Labels := by
      have ha : raw19177step3 = raw19177step2 := by apply Matrix.ext; unfold raw19177step3 raw19177step2; decide +kernel
      have hl : raw19177step2Labels = labelEmbedding7 ∘ raw19177step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19177step2 raw19177step2Labels raw19177step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw19178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19178step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19178step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19178 raw19178Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw19178 raw19178Labels = mixedMoment B raw19178step0 raw19178step0Labels := by
      have ha : raw19178step0 = (fun i j => raw19178 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19178step0 raw19178; decide +kernel
      have hl : raw19178step0Labels = raw19178Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19178 raw19178Labels permutation170 permutation3
    mixedMoment B raw19178step0 raw19178step0Labels = mixedMoment B raw19178step1 raw19178step1Labels := by
      have ha : raw19178step1 = raw19178step0 := by apply Matrix.ext; unfold raw19178step1 raw19178step0; decide +kernel
      have hl : raw19178step0Labels = labelEmbedding6 ∘ raw19178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19178step0 raw19178step0Labels raw19178step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

def raw19179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19179step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19179 raw19179Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw19179 raw19179Labels = mixedMoment B raw19179step0 raw19179step0Labels := by
      have ha : raw19179step0 = (fun i j => raw19179 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19179step0 raw19179; decide +kernel
      have hl : raw19179step0Labels = raw19179Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19179 raw19179Labels permutation170 permutation3
    mixedMoment B raw19179step0 raw19179step0Labels = mixedMoment B raw19179step1 raw19179step1Labels := by
      have ha : raw19179step1 = raw19179step0 := by apply Matrix.ext; unfold raw19179step1 raw19179step0; decide +kernel
      have hl : raw19179step0Labels = labelEmbedding6 ∘ raw19179step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19179step0 raw19179step0Labels raw19179step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw19180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19180step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19180step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19180 raw19180Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw19180 raw19180Labels = mixedMoment B raw19180step0 raw19180step0Labels := by
      have hz : ∀ j, raw19180 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19180step0 = (fun i j => raw19180 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19180step0 raw19180; decide +kernel
      have hl : raw19180step0Labels = raw19180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19180 raw19180Labels permutation434 hz
    mixedMoment B raw19180step0 raw19180step0Labels = mixedMoment B raw19180step1 raw19180step1Labels := by
      have ha : raw19180step1 = (fun i j => raw19180step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19180step1 raw19180step0; decide +kernel
      have hl : raw19180step1Labels = raw19180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19180step0 raw19180step0Labels permutation36 permutation3
    mixedMoment B raw19180step1 raw19180step1Labels = mixedMoment B raw19180step2 raw19180step2Labels := by
      have ha : raw19180step2 = raw19180step1 := by apply Matrix.ext; unfold raw19180step2 raw19180step1; decide +kernel
      have hl : raw19180step1Labels = labelEmbedding6 ∘ raw19180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19180step1 raw19180step1Labels raw19180step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw19181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19181step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19181step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19181 raw19181Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw19181 raw19181Labels = mixedMoment B raw19181step0 raw19181step0Labels := by
      have hz : ∀ j, raw19181 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19181step0 = (fun i j => raw19181 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19181step0 raw19181; decide +kernel
      have hl : raw19181step0Labels = raw19181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19181 raw19181Labels permutation520 hz
    mixedMoment B raw19181step0 raw19181step0Labels = mixedMoment B raw19181step1 raw19181step1Labels := by
      have ha : raw19181step1 = (fun i j => raw19181step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19181step1 raw19181step0; decide +kernel
      have hl : raw19181step1Labels = raw19181step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19181step0 raw19181step0Labels permutation36 permutation3
    mixedMoment B raw19181step1 raw19181step1Labels = mixedMoment B raw19181step2 raw19181step2Labels := by
      have ha : raw19181step2 = raw19181step1 := by apply Matrix.ext; unfold raw19181step2 raw19181step1; decide +kernel
      have hl : raw19181step1Labels = labelEmbedding6 ∘ raw19181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19181step1 raw19181step1Labels raw19181step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw19182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19182step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19182step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19182step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19182step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19182 raw19182Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw19182 raw19182Labels = mixedMoment B raw19182step0 raw19182step0Labels := by
      have ha : raw19182step0 = (fun i j => raw19182 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19182step0 raw19182; decide +kernel
      have hl : raw19182step0Labels = raw19182Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19182 raw19182Labels permutation246 permutation5
    mixedMoment B raw19182step0 raw19182step0Labels = mixedMoment B raw19182step1 raw19182step1Labels := by
      have ha : raw19182step1 = -raw19182step0 := by apply Matrix.ext; change ∀ i j, raw19182step1 i j = -(raw19182step0 i j); unfold raw19182step1 raw19182step0; decide +kernel
      have hl : raw19182step1Labels = raw19182step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19182step1 raw19182step1Labels = mixedMoment B raw19182step2 raw19182step2Labels := by
      have ha : raw19182step2 = raw19182step1 := by apply Matrix.ext; unfold raw19182step2 raw19182step1; decide +kernel
      have hl : raw19182step1Labels = labelEmbedding8 ∘ raw19182step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19182step1 raw19182step1Labels raw19182step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw19183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19183step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19183 raw19183Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw19183 raw19183Labels = mixedMoment B raw19183step0 raw19183step0Labels := by
      have hz : ∀ j, raw19183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19183step0 = (fun i j => raw19183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19183step0 raw19183; decide +kernel
      have hl : raw19183step0Labels = raw19183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19183 raw19183Labels permutation346 hz
    mixedMoment B raw19183step0 raw19183step0Labels = mixedMoment B raw19183step1 raw19183step1Labels := by
      have ha : raw19183step1 = (fun i j => raw19183step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19183step1 raw19183step0; decide +kernel
      have hl : raw19183step1Labels = raw19183step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19183step0 raw19183step0Labels permutation37 permutation3
    mixedMoment B raw19183step1 raw19183step1Labels = mixedMoment B raw19183step2 raw19183step2Labels := by
      have ha : raw19183step2 = raw19183step1 := by apply Matrix.ext; unfold raw19183step2 raw19183step1; decide +kernel
      have hl : raw19183step1Labels = labelEmbedding6 ∘ raw19183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19183step1 raw19183step1Labels raw19183step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

def raw19184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19184step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19184step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19184 raw19184Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw19184 raw19184Labels = mixedMoment B raw19184step0 raw19184step0Labels := by
      have hz : ∀ j, raw19184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19184step0 = (fun i j => raw19184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19184step0 raw19184; decide +kernel
      have hl : raw19184step0Labels = raw19184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19184 raw19184Labels permutation346 hz
    mixedMoment B raw19184step0 raw19184step0Labels = mixedMoment B raw19184step1 raw19184step1Labels := by
      have ha : raw19184step1 = (fun i j => raw19184step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19184step1 raw19184step0; decide +kernel
      have hl : raw19184step1Labels = raw19184step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19184step0 raw19184step0Labels permutation37 permutation3
    mixedMoment B raw19184step1 raw19184step1Labels = mixedMoment B raw19184step2 raw19184step2Labels := by
      have ha : raw19184step2 = raw19184step1 := by apply Matrix.ext; unfold raw19184step2 raw19184step1; decide +kernel
      have hl : raw19184step1Labels = labelEmbedding6 ∘ raw19184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19184step1 raw19184step1Labels raw19184step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw19185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19185step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19185 raw19185Labels = mixedMoment B node5398 node5398Labels := by
  calc
    mixedMoment B raw19185 raw19185Labels = mixedMoment B raw19185step0 raw19185step0Labels := by
      have ha : raw19185step0 = (fun i j => raw19185 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19185step0 raw19185; decide +kernel
      have hl : raw19185step0Labels = raw19185Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19185 raw19185Labels permutation181 permutation3
    mixedMoment B raw19185step0 raw19185step0Labels = mixedMoment B raw19185step1 raw19185step1Labels := by
      have ha : raw19185step1 = raw19185step0 := by apply Matrix.ext; unfold raw19185step1 raw19185step0; decide +kernel
      have hl : raw19185step0Labels = labelEmbedding6 ∘ raw19185step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19185step0 raw19185step0Labels raw19185step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5398 node5398Labels := by rfl

def raw19186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw19186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19186step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19186step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19186 raw19186Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw19186 raw19186Labels = mixedMoment B raw19186step0 raw19186step0Labels := by
      have hz : ∀ j, raw19186 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19186step0 = (fun i j => raw19186 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19186step0 raw19186; decide +kernel
      have hl : raw19186step0Labels = raw19186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19186 raw19186Labels permutation520 hz
    mixedMoment B raw19186step0 raw19186step0Labels = mixedMoment B raw19186step1 raw19186step1Labels := by
      have hz : ∀ j, raw19186step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19186step1 = (fun i j => raw19186step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19186step1 raw19186step0; decide +kernel
      have hl : raw19186step1Labels = raw19186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19186step0 raw19186step0Labels permutation80 hz
    mixedMoment B raw19186step1 raw19186step1Labels = mixedMoment B raw19186step2 raw19186step2Labels := by
      have ha : raw19186step2 = (fun i j => raw19186step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19186step2 raw19186step1; decide +kernel
      have hl : raw19186step2Labels = raw19186step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19186step1 raw19186step1Labels permutation9 permutation3
    mixedMoment B raw19186step2 raw19186step2Labels = mixedMoment B raw19186step3 raw19186step3Labels := by
      have ha : raw19186step3 = raw19186step2 := by apply Matrix.ext; unfold raw19186step3 raw19186step2; decide +kernel
      have hl : raw19186step2Labels = labelEmbedding6 ∘ raw19186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19186step2 raw19186step2Labels raw19186step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

def raw19187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19187step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19187step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19187step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19187step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19187 raw19187Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw19187 raw19187Labels = mixedMoment B raw19187step0 raw19187step0Labels := by
      have hz : ∀ j, raw19187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19187step0 = (fun i j => raw19187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19187step0 raw19187; decide +kernel
      have hl : raw19187step0Labels = raw19187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19187 raw19187Labels permutation346 hz
    mixedMoment B raw19187step0 raw19187step0Labels = mixedMoment B raw19187step1 raw19187step1Labels := by
      have ha : raw19187step1 = (fun i j => raw19187step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19187step1 raw19187step0; decide +kernel
      have hl : raw19187step1Labels = raw19187step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19187step0 raw19187step0Labels permutation51 permutation5
    mixedMoment B raw19187step1 raw19187step1Labels = mixedMoment B raw19187step2 raw19187step2Labels := by
      have ha : raw19187step2 = -raw19187step1 := by apply Matrix.ext; change ∀ i j, raw19187step2 i j = -(raw19187step1 i j); unfold raw19187step2 raw19187step1; decide +kernel
      have hl : raw19187step2Labels = raw19187step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19187step2 raw19187step2Labels = mixedMoment B raw19187step3 raw19187step3Labels := by
      have ha : raw19187step3 = raw19187step2 := by apply Matrix.ext; unfold raw19187step3 raw19187step2; decide +kernel
      have hl : raw19187step2Labels = labelEmbedding8 ∘ raw19187step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19187step2 raw19187step2Labels raw19187step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw19188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19188step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19188step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19188 raw19188Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw19188 raw19188Labels = mixedMoment B raw19188step0 raw19188step0Labels := by
      have hz : ∀ j, raw19188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19188step0 = (fun i j => raw19188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19188step0 raw19188; decide +kernel
      have hl : raw19188step0Labels = raw19188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19188 raw19188Labels permutation346 hz
    mixedMoment B raw19188step0 raw19188step0Labels = mixedMoment B raw19188step1 raw19188step1Labels := by
      have ha : raw19188step1 = (fun i j => raw19188step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19188step1 raw19188step0; decide +kernel
      have hl : raw19188step1Labels = raw19188step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19188step0 raw19188step0Labels permutation36 permutation3
    mixedMoment B raw19188step1 raw19188step1Labels = mixedMoment B raw19188step2 raw19188step2Labels := by
      have ha : raw19188step2 = raw19188step1 := by apply Matrix.ext; unfold raw19188step2 raw19188step1; decide +kernel
      have hl : raw19188step1Labels = labelEmbedding6 ∘ raw19188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19188step1 raw19188step1Labels raw19188step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

def raw19189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19189step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19189 raw19189Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw19189 raw19189Labels = mixedMoment B raw19189step0 raw19189step0Labels := by
      have hz : ∀ j, raw19189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19189step0 = (fun i j => raw19189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19189step0 raw19189; decide +kernel
      have hl : raw19189step0Labels = raw19189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19189 raw19189Labels permutation346 hz
    mixedMoment B raw19189step0 raw19189step0Labels = mixedMoment B raw19189step1 raw19189step1Labels := by
      have ha : raw19189step1 = (fun i j => raw19189step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19189step1 raw19189step0; decide +kernel
      have hl : raw19189step1Labels = raw19189step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19189step0 raw19189step0Labels permutation36 permutation3
    mixedMoment B raw19189step1 raw19189step1Labels = mixedMoment B raw19189step2 raw19189step2Labels := by
      have ha : raw19189step2 = raw19189step1 := by apply Matrix.ext; unfold raw19189step2 raw19189step1; decide +kernel
      have hl : raw19189step1Labels = labelEmbedding6 ∘ raw19189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19189step1 raw19189step1Labels raw19189step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw19190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19190step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19190 raw19190Labels = mixedMoment B node5398 node5398Labels := by
  calc
    mixedMoment B raw19190 raw19190Labels = mixedMoment B raw19190step0 raw19190step0Labels := by
      have ha : raw19190step0 = (fun i j => raw19190 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19190step0 raw19190; decide +kernel
      have hl : raw19190step0Labels = raw19190Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19190 raw19190Labels permutation180 permutation3
    mixedMoment B raw19190step0 raw19190step0Labels = mixedMoment B raw19190step1 raw19190step1Labels := by
      have ha : raw19190step1 = raw19190step0 := by apply Matrix.ext; unfold raw19190step1 raw19190step0; decide +kernel
      have hl : raw19190step0Labels = labelEmbedding6 ∘ raw19190step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19190step0 raw19190step0Labels raw19190step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5398 node5398Labels := by rfl

def raw19191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw19191step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19191step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19191step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19191step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19191step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19191 raw19191Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw19191 raw19191Labels = mixedMoment B raw19191step0 raw19191step0Labels := by
      have hz : ∀ j, raw19191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19191step0 = (fun i j => raw19191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19191step0 raw19191; decide +kernel
      have hl : raw19191step0Labels = raw19191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19191 raw19191Labels permutation434 hz
    mixedMoment B raw19191step0 raw19191step0Labels = mixedMoment B raw19191step1 raw19191step1Labels := by
      have hz : ∀ j, raw19191step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19191step1 = (fun i j => raw19191step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19191step1 raw19191step0; decide +kernel
      have hl : raw19191step1Labels = raw19191step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19191step0 raw19191step0Labels permutation80 hz
    mixedMoment B raw19191step1 raw19191step1Labels = mixedMoment B raw19191step2 raw19191step2Labels := by
      have ha : raw19191step2 = (fun i j => raw19191step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19191step2 raw19191step1; decide +kernel
      have hl : raw19191step2Labels = raw19191step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19191step1 raw19191step1Labels permutation9 permutation3
    mixedMoment B raw19191step2 raw19191step2Labels = mixedMoment B raw19191step3 raw19191step3Labels := by
      have ha : raw19191step3 = raw19191step2 := by apply Matrix.ext; unfold raw19191step3 raw19191step2; decide +kernel
      have hl : raw19191step2Labels = labelEmbedding6 ∘ raw19191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19191step2 raw19191step2Labels raw19191step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

def raw19192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw19192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw19192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19192step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19192step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19192step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19192step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19192 raw19192Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw19192 raw19192Labels = mixedMoment B raw19192step0 raw19192step0Labels := by
      have hz : ∀ j, raw19192 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19192step0 = (fun i j => raw19192 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19192step0 raw19192; decide +kernel
      have hl : raw19192step0Labels = raw19192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19192 raw19192Labels permutation346 hz
    mixedMoment B raw19192step0 raw19192step0Labels = mixedMoment B raw19192step1 raw19192step1Labels := by
      have ha : raw19192step1 = (fun i j => raw19192step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19192step1 raw19192step0; decide +kernel
      have hl : raw19192step1Labels = raw19192step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19192step0 raw19192step0Labels permutation50 permutation5
    mixedMoment B raw19192step1 raw19192step1Labels = mixedMoment B raw19192step2 raw19192step2Labels := by
      have ha : raw19192step2 = -raw19192step1 := by apply Matrix.ext; change ∀ i j, raw19192step2 i j = -(raw19192step1 i j); unfold raw19192step2 raw19192step1; decide +kernel
      have hl : raw19192step2Labels = raw19192step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19192step2 raw19192step2Labels = mixedMoment B raw19192step3 raw19192step3Labels := by
      have ha : raw19192step3 = raw19192step2 := by apply Matrix.ext; unfold raw19192step3 raw19192step2; decide +kernel
      have hl : raw19192step2Labels = labelEmbedding8 ∘ raw19192step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19192step2 raw19192step2Labels raw19192step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw19193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19193 raw19193Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw19193 raw19193Labels = mixedMoment B raw19193step0 raw19193step0Labels := by
      have hz : ∀ j, raw19193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19193step0 = (fun i j => raw19193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19193step0 raw19193; decide +kernel
      have hl : raw19193step0Labels = raw19193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19193 raw19193Labels permutation346 hz
    mixedMoment B raw19193step0 raw19193step0Labels = mixedMoment B raw19193step1 raw19193step1Labels := by
      have ha : raw19193step1 = (fun i j => raw19193step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19193step1 raw19193step0; decide +kernel
      have hl : raw19193step1Labels = raw19193step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19193step0 raw19193step0Labels permutation56 permutation2
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw19194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19194step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19194 raw19194Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw19194 raw19194Labels = mixedMoment B raw19194step0 raw19194step0Labels := by
      have ha : raw19194step0 = (fun i j => raw19194 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19194step0 raw19194; decide +kernel
      have hl : raw19194step0Labels = raw19194Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19194 raw19194Labels permutation176 permutation3
    mixedMoment B raw19194step0 raw19194step0Labels = mixedMoment B raw19194step1 raw19194step1Labels := by
      have ha : raw19194step1 = raw19194step0 := by apply Matrix.ext; unfold raw19194step1 raw19194step0; decide +kernel
      have hl : raw19194step0Labels = labelEmbedding6 ∘ raw19194step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19194step0 raw19194step0Labels raw19194step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw19195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw19195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw19195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw19195step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19195step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw19195step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19195 raw19195Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw19195 raw19195Labels = mixedMoment B raw19195step0 raw19195step0Labels := by
      have hz : ∀ j, raw19195 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19195step0 = (fun i j => raw19195 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19195step0 raw19195; decide +kernel
      have hl : raw19195step0Labels = raw19195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19195 raw19195Labels permutation520 hz
    mixedMoment B raw19195step0 raw19195step0Labels = mixedMoment B raw19195step1 raw19195step1Labels := by
      have hz : ∀ j, raw19195step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19195step1 = (fun i j => raw19195step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19195step1 raw19195step0; decide +kernel
      have hl : raw19195step1Labels = raw19195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19195step0 raw19195step0Labels permutation80 hz
    mixedMoment B raw19195step1 raw19195step1Labels = mixedMoment B raw19195step2 raw19195step2Labels := by
      have ha : raw19195step2 = (fun i j => raw19195step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19195step2 raw19195step1; decide +kernel
      have hl : raw19195step2Labels = raw19195step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19195step1 raw19195step1Labels permutation31 permutation2
    mixedMoment B raw19195step2 raw19195step2Labels = mixedMoment B raw19195step3 raw19195step3Labels := by
      have ha : raw19195step3 = -raw19195step2 := by apply Matrix.ext; change ∀ i j, raw19195step3 i j = -(raw19195step2 i j); unfold raw19195step3 raw19195step2; decide +kernel
      have hl : raw19195step3Labels = raw19195step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw19196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19196step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19196step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19196step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19196 raw19196Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw19196 raw19196Labels = mixedMoment B raw19196step0 raw19196step0Labels := by
      have ha : raw19196step0 = (fun i j => raw19196 (permutation313 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19196step0 raw19196; decide +kernel
      have hl : raw19196step0Labels = raw19196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19196 raw19196Labels permutation313 permutation5
    mixedMoment B raw19196step0 raw19196step0Labels = mixedMoment B raw19196step1 raw19196step1Labels := by
      have ha : raw19196step1 = -raw19196step0 := by apply Matrix.ext; change ∀ i j, raw19196step1 i j = -(raw19196step0 i j); unfold raw19196step1 raw19196step0; decide +kernel
      have hl : raw19196step1Labels = raw19196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19196step1 raw19196step1Labels = mixedMoment B raw19196step2 raw19196step2Labels := by
      have ha : raw19196step2 = raw19196step1 := by apply Matrix.ext; unfold raw19196step2 raw19196step1; decide +kernel
      have hl : raw19196step1Labels = labelEmbedding8 ∘ raw19196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19196step1 raw19196step1Labels raw19196step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw19197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19197step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19197step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19197step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19197 raw19197Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw19197 raw19197Labels = mixedMoment B raw19197step0 raw19197step0Labels := by
      have ha : raw19197step0 = (fun i j => raw19197 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19197step0 raw19197; decide +kernel
      have hl : raw19197step0Labels = raw19197Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19197 raw19197Labels permutation194 permutation7
    mixedMoment B raw19197step0 raw19197step0Labels = mixedMoment B raw19197step1 raw19197step1Labels := by
      have ha : raw19197step1 = -raw19197step0 := by apply Matrix.ext; change ∀ i j, raw19197step1 i j = -(raw19197step0 i j); unfold raw19197step1 raw19197step0; decide +kernel
      have hl : raw19197step1Labels = raw19197step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19197step1 raw19197step1Labels = mixedMoment B raw19197step2 raw19197step2Labels := by
      have ha : raw19197step2 = raw19197step1 := by apply Matrix.ext; unfold raw19197step2 raw19197step1; decide +kernel
      have hl : raw19197step1Labels = labelEmbedding10 ∘ raw19197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19197step1 raw19197step1Labels raw19197step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw19198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19198step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19198step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19198step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19198step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19198 raw19198Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19198 raw19198Labels = mixedMoment B raw19198step0 raw19198step0Labels := by
      have ha : raw19198step0 = (fun i j => raw19198 (permutation317 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19198step0 raw19198; decide +kernel
      have hl : raw19198step0Labels = raw19198Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19198 raw19198Labels permutation317 permutation4
    mixedMoment B raw19198step0 raw19198step0Labels = mixedMoment B raw19198step1 raw19198step1Labels := by
      have ha : raw19198step1 = -raw19198step0 := by apply Matrix.ext; change ∀ i j, raw19198step1 i j = -(raw19198step0 i j); unfold raw19198step1 raw19198step0; decide +kernel
      have hl : raw19198step1Labels = raw19198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19198step1 raw19198step1Labels = mixedMoment B raw19198step2 raw19198step2Labels := by
      have ha : raw19198step2 = raw19198step1 := by apply Matrix.ext; unfold raw19198step2 raw19198step1; decide +kernel
      have hl : raw19198step1Labels = labelEmbedding7 ∘ raw19198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19198step1 raw19198step1Labels raw19198step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw19199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19199step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19199step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19199step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19199step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19199 raw19199Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19199 raw19199Labels = mixedMoment B raw19199step0 raw19199step0Labels := by
      have ha : raw19199step0 = (fun i j => raw19199 (permutation328 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19199step0 raw19199; decide +kernel
      have hl : raw19199step0Labels = raw19199Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19199 raw19199Labels permutation328 permutation4
    mixedMoment B raw19199step0 raw19199step0Labels = mixedMoment B raw19199step1 raw19199step1Labels := by
      have ha : raw19199step1 = -raw19199step0 := by apply Matrix.ext; change ∀ i j, raw19199step1 i j = -(raw19199step0 i j); unfold raw19199step1 raw19199step0; decide +kernel
      have hl : raw19199step1Labels = raw19199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19199step1 raw19199step1Labels = mixedMoment B raw19199step2 raw19199step2Labels := by
      have ha : raw19199step2 = raw19199step1 := by apply Matrix.ext; unfold raw19199step2 raw19199step1; decide +kernel
      have hl : raw19199step1Labels = labelEmbedding7 ∘ raw19199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19199step1 raw19199step1Labels raw19199step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
