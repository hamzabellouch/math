import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw384 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw384Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw384step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw384step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw384 raw384Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw384 raw384Labels = mixedMoment B raw384step0 raw384step0Labels := by
      have ha : raw384step0 = (fun i j => raw384 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw384step0 raw384; decide +kernel
      have hl : raw384step0Labels = raw384Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw384 raw384Labels permutation8 permutation5
    mixedMoment B raw384step0 raw384step0Labels = mixedMoment B raw384step1 raw384step1Labels := by
      have ha : raw384step1 = raw384step0 := by apply Matrix.ext; unfold raw384step1 raw384step0; decide +kernel
      have hl : raw384step0Labels = labelEmbedding1 ∘ raw384step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw384step0 raw384step0Labels raw384step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw385 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw385Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw385step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw385step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw385 raw385Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw385 raw385Labels = mixedMoment B raw385step0 raw385step0Labels := by
      have ha : raw385step0 = (fun i j => raw385 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw385step0 raw385; decide +kernel
      have hl : raw385step0Labels = raw385Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw385 raw385Labels permutation8 permutation4
    _ = mixedMoment B node402 node402Labels := by rfl

def raw386 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1]]
def raw386Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw386step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw386 raw386Labels = mixedMoment B node3105 node3105Labels := by
  calc
    mixedMoment B raw386 raw386Labels = mixedMoment B raw386step0 raw386step0Labels := by
      have ha : raw386step0 = (fun i j => raw386 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw386step0 raw386; decide +kernel
      have hl : raw386step0Labels = raw386Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw386 raw386Labels permutation152 permutation5
    mixedMoment B raw386step0 raw386step0Labels = mixedMoment B raw386step1 raw386step1Labels := by
      have ha : raw386step1 = raw386step0 := by apply Matrix.ext; unfold raw386step1 raw386step0; decide +kernel
      have hl : raw386step0Labels = labelEmbedding1 ∘ raw386step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw386step0 raw386step0Labels raw386step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3105 node3105Labels := by rfl

def raw387 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1]]
def raw387Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw387step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw387 raw387Labels = mixedMoment B node371 node371Labels := by
  calc
    mixedMoment B raw387 raw387Labels = mixedMoment B raw387step0 raw387step0Labels := by
      have ha : raw387step0 = (fun i j => raw387 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw387step0 raw387; decide +kernel
      have hl : raw387step0Labels = raw387Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw387 raw387Labels permutation155 permutation4
    _ = mixedMoment B node371 node371Labels := by rfl

def raw388 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 2, -2]]
def raw388Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw388step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw388 raw388Labels = mixedMoment B node3106 node3106Labels := by
  calc
    mixedMoment B raw388 raw388Labels = mixedMoment B raw388step0 raw388step0Labels := by
      have ha : raw388step0 = (fun i j => raw388 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw388step0 raw388; decide +kernel
      have hl : raw388step0Labels = raw388Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw388 raw388Labels permutation32 permutation5
    mixedMoment B raw388step0 raw388step0Labels = mixedMoment B raw388step1 raw388step1Labels := by
      have ha : raw388step1 = raw388step0 := by apply Matrix.ext; unfold raw388step1 raw388step0; decide +kernel
      have hl : raw388step0Labels = labelEmbedding1 ∘ raw388step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw388step0 raw388step0Labels raw388step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3106 node3106Labels := by rfl

def raw389 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 2, -2]]
def raw389Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw389step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw389 raw389Labels = mixedMoment B node372 node372Labels := by
  calc
    mixedMoment B raw389 raw389Labels = mixedMoment B raw389step0 raw389step0Labels := by
      have ha : raw389step0 = (fun i j => raw389 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw389step0 raw389; decide +kernel
      have hl : raw389step0Labels = raw389Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw389 raw389Labels permutation32 permutation4
    _ = mixedMoment B node372 node372Labels := by rfl

def raw390 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0]]
def raw390Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw390step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw390step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw390 raw390Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw390 raw390Labels = mixedMoment B raw390step0 raw390step0Labels := by
      have ha : raw390step0 = (fun i j => raw390 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw390step0 raw390; decide +kernel
      have hl : raw390step0Labels = raw390Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw390 raw390Labels permutation32 permutation5
    mixedMoment B raw390step0 raw390step0Labels = mixedMoment B raw390step1 raw390step1Labels := by
      have ha : raw390step1 = raw390step0 := by apply Matrix.ext; unfold raw390step1 raw390step0; decide +kernel
      have hl : raw390step0Labels = labelEmbedding1 ∘ raw390step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw390step0 raw390step0Labels raw390step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw391 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0]]
def raw391Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw391step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw391 raw391Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw391 raw391Labels = mixedMoment B raw391step0 raw391step0Labels := by
      have ha : raw391step0 = (fun i j => raw391 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw391step0 raw391; decide +kernel
      have hl : raw391step0Labels = raw391Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw391 raw391Labels permutation37 permutation4
    _ = mixedMoment B node387 node387Labels := by rfl

def raw392 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw392step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw392step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw392 raw392Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw392 raw392Labels = mixedMoment B raw392step0 raw392step0Labels := by
      have ha : raw392step0 = (fun i j => raw392 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw392step0 raw392; decide +kernel
      have hl : raw392step0Labels = raw392Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw392 raw392Labels permutation8 permutation5
    mixedMoment B raw392step0 raw392step0Labels = mixedMoment B raw392step1 raw392step1Labels := by
      have ha : raw392step1 = raw392step0 := by apply Matrix.ext; unfold raw392step1 raw392step0; decide +kernel
      have hl : raw392step0Labels = labelEmbedding1 ∘ raw392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw392step0 raw392step0Labels raw392step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw393 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw393Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw393step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw393step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw393 raw393Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw393 raw393Labels = mixedMoment B raw393step0 raw393step0Labels := by
      have ha : raw393step0 = (fun i j => raw393 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw393step0 raw393; decide +kernel
      have hl : raw393step0Labels = raw393Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw393 raw393Labels permutation8 permutation4
    _ = mixedMoment B node390 node390Labels := by rfl

def raw394 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw394step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw394step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw394 raw394Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw394 raw394Labels = mixedMoment B raw394step0 raw394step0Labels := by
      have ha : raw394step0 = (fun i j => raw394 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw394step0 raw394; decide +kernel
      have hl : raw394step0Labels = raw394Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw394 raw394Labels permutation8 permutation5
    mixedMoment B raw394step0 raw394step0Labels = mixedMoment B raw394step1 raw394step1Labels := by
      have ha : raw394step1 = raw394step0 := by apply Matrix.ext; unfold raw394step1 raw394step0; decide +kernel
      have hl : raw394step0Labels = labelEmbedding1 ∘ raw394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw394step0 raw394step0Labels raw394step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw395 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw395Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw395step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw395step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw395 raw395Labels = mixedMoment B node388 node388Labels := by
  calc
    mixedMoment B raw395 raw395Labels = mixedMoment B raw395step0 raw395step0Labels := by
      have ha : raw395step0 = (fun i j => raw395 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw395step0 raw395; decide +kernel
      have hl : raw395step0Labels = raw395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw395 raw395Labels permutation8 permutation4
    _ = mixedMoment B node388 node388Labels := by rfl

def raw396 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1]]
def raw396Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw396step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw396 raw396Labels = mixedMoment B node3116 node3116Labels := by
  calc
    mixedMoment B raw396 raw396Labels = mixedMoment B raw396step0 raw396step0Labels := by
      have ha : raw396step0 = (fun i j => raw396 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw396step0 raw396; decide +kernel
      have hl : raw396step0Labels = raw396Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw396 raw396Labels permutation32 permutation5
    mixedMoment B raw396step0 raw396step0Labels = mixedMoment B raw396step1 raw396step1Labels := by
      have ha : raw396step1 = raw396step0 := by apply Matrix.ext; unfold raw396step1 raw396step0; decide +kernel
      have hl : raw396step0Labels = labelEmbedding1 ∘ raw396step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw396step0 raw396step0Labels raw396step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3116 node3116Labels := by rfl

def raw397 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1]]
def raw397Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw397step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw397 raw397Labels = mixedMoment B node368 node368Labels := by
  calc
    mixedMoment B raw397 raw397Labels = mixedMoment B raw397step0 raw397step0Labels := by
      have ha : raw397step0 = (fun i j => raw397 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw397step0 raw397; decide +kernel
      have hl : raw397step0Labels = raw397Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw397 raw397Labels permutation35 permutation4
    _ = mixedMoment B node368 node368Labels := by rfl

def raw398 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 2, -2]]
def raw398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw398step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw398step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw398 raw398Labels = mixedMoment B node3117 node3117Labels := by
  calc
    mixedMoment B raw398 raw398Labels = mixedMoment B raw398step0 raw398step0Labels := by
      have ha : raw398step0 = (fun i j => raw398 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw398step0 raw398; decide +kernel
      have hl : raw398step0Labels = raw398Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw398 raw398Labels permutation8 permutation5
    mixedMoment B raw398step0 raw398step0Labels = mixedMoment B raw398step1 raw398step1Labels := by
      have ha : raw398step1 = raw398step0 := by apply Matrix.ext; unfold raw398step1 raw398step0; decide +kernel
      have hl : raw398step0Labels = labelEmbedding1 ∘ raw398step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw398step0 raw398step0Labels raw398step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3117 node3117Labels := by rfl

def raw399 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 2, -2]]
def raw399Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw399step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw399step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw399 raw399Labels = mixedMoment B node369 node369Labels := by
  calc
    mixedMoment B raw399 raw399Labels = mixedMoment B raw399step0 raw399step0Labels := by
      have ha : raw399step0 = (fun i j => raw399 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw399step0 raw399; decide +kernel
      have hl : raw399step0Labels = raw399Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw399 raw399Labels permutation8 permutation4
    _ = mixedMoment B node369 node369Labels := by rfl

def raw400 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1]]
def raw400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw400step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw400step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw400 raw400Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw400 raw400Labels = mixedMoment B raw400step0 raw400step0Labels := by
      have ha : raw400step0 = (fun i j => raw400 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw400step0 raw400; decide +kernel
      have hl : raw400step0Labels = raw400Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw400 raw400Labels permutation8 permutation5
    mixedMoment B raw400step0 raw400step0Labels = mixedMoment B raw400step1 raw400step1Labels := by
      have ha : raw400step1 = raw400step0 := by apply Matrix.ext; unfold raw400step1 raw400step0; decide +kernel
      have hl : raw400step0Labels = labelEmbedding1 ∘ raw400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw400step0 raw400step0Labels raw400step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw401 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1]]
def raw401Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw401step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw401step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw401 raw401Labels = mixedMoment B node414 node414Labels := by
  calc
    mixedMoment B raw401 raw401Labels = mixedMoment B raw401step0 raw401step0Labels := by
      have ha : raw401step0 = (fun i j => raw401 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw401step0 raw401; decide +kernel
      have hl : raw401step0Labels = raw401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw401 raw401Labels permutation13 permutation4
    _ = mixedMoment B node414 node414Labels := by rfl

def raw402 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0]]
def raw402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw402step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw402step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw402 raw402Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw402 raw402Labels = mixedMoment B raw402step0 raw402step0Labels := by
      have ha : raw402step0 = (fun i j => raw402 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw402step0 raw402; decide +kernel
      have hl : raw402step0Labels = raw402Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw402 raw402Labels permutation8 permutation5
    mixedMoment B raw402step0 raw402step0Labels = mixedMoment B raw402step1 raw402step1Labels := by
      have ha : raw402step1 = raw402step0 := by apply Matrix.ext; unfold raw402step1 raw402step0; decide +kernel
      have hl : raw402step0Labels = labelEmbedding1 ∘ raw402step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw402step0 raw402step0Labels raw402step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw403 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0]]
def raw403Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw403step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw403step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw403 raw403Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw403 raw403Labels = mixedMoment B raw403step0 raw403step0Labels := by
      have ha : raw403step0 = (fun i j => raw403 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw403step0 raw403; decide +kernel
      have hl : raw403step0Labels = raw403Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw403 raw403Labels permutation11 permutation4
    _ = mixedMoment B node416 node416Labels := by rfl

def raw404 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw404step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw404step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw404step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw404 raw404Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw404 raw404Labels = mixedMoment B raw404step0 raw404step0Labels := by
      have ha : raw404step0 = (fun i j => raw404 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw404step0 raw404; decide +kernel
      have hl : raw404step0Labels = raw404Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw404 raw404Labels permutation2 permutation5
    mixedMoment B raw404step0 raw404step0Labels = mixedMoment B raw404step1 raw404step1Labels := by
      have ha : raw404step1 = raw404step0 := by apply Matrix.ext; unfold raw404step1 raw404step0; decide +kernel
      have hl : raw404step0Labels = labelEmbedding1 ∘ raw404step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw404step0 raw404step0Labels raw404step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3121 node3121Labels := by rfl

def raw405 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw405Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw405step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw405step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw405 raw405Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw405 raw405Labels = mixedMoment B raw405step0 raw405step0Labels := by
      have ha : raw405step0 = (fun i j => raw405 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw405step0 raw405; decide +kernel
      have hl : raw405step0Labels = raw405Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw405 raw405Labels permutation2 permutation4
    _ = mixedMoment B node420 node420Labels := by rfl

def raw406 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw406step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw406step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw406step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw406 raw406Labels = mixedMoment B node3125 node3125Labels := by
  calc
    mixedMoment B raw406 raw406Labels = mixedMoment B raw406step0 raw406step0Labels := by
      have ha : raw406step0 = (fun i j => raw406 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw406step0 raw406; decide +kernel
      have hl : raw406step0Labels = raw406Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw406 raw406Labels permutation2 permutation5
    mixedMoment B raw406step0 raw406step0Labels = mixedMoment B raw406step1 raw406step1Labels := by
      have ha : raw406step1 = raw406step0 := by apply Matrix.ext; unfold raw406step1 raw406step0; decide +kernel
      have hl : raw406step0Labels = labelEmbedding1 ∘ raw406step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw406step0 raw406step0Labels raw406step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3125 node3125Labels := by rfl

def raw407 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw407Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw407step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw407step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw407 raw407Labels = mixedMoment B node415 node415Labels := by
  calc
    mixedMoment B raw407 raw407Labels = mixedMoment B raw407step0 raw407step0Labels := by
      have ha : raw407step0 = (fun i j => raw407 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw407step0 raw407; decide +kernel
      have hl : raw407step0Labels = raw407Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw407 raw407Labels permutation2 permutation4
    _ = mixedMoment B node415 node415Labels := by rfl

def raw408 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw408 raw408Labels = mixedMoment B node3139 node3139Labels := by
  calc
    mixedMoment B raw408 raw408Labels = mixedMoment B raw408step0 raw408step0Labels := by
      have ha : raw408step0 = (fun i j => raw408 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw408step0 raw408; decide +kernel
      have hl : raw408step0Labels = raw408Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw408 raw408Labels permutation152 permutation5
    mixedMoment B raw408step0 raw408step0Labels = mixedMoment B raw408step1 raw408step1Labels := by
      have ha : raw408step1 = raw408step0 := by apply Matrix.ext; unfold raw408step1 raw408step0; decide +kernel
      have hl : raw408step0Labels = labelEmbedding1 ∘ raw408step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw408step0 raw408step0Labels raw408step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3139 node3139Labels := by rfl

def raw409 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw409Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw409step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw409 raw409Labels = mixedMoment B node174 node174Labels := by
  calc
    mixedMoment B raw409 raw409Labels = mixedMoment B raw409step0 raw409step0Labels := by
      have ha : raw409step0 = (fun i j => raw409 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw409step0 raw409; decide +kernel
      have hl : raw409step0Labels = raw409Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw409 raw409Labels permutation164 permutation4
    _ = mixedMoment B node174 node174Labels := by rfl

def raw410 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw410 raw410Labels = mixedMoment B node3140 node3140Labels := by
  calc
    mixedMoment B raw410 raw410Labels = mixedMoment B raw410step0 raw410step0Labels := by
      have ha : raw410step0 = (fun i j => raw410 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw410step0 raw410; decide +kernel
      have hl : raw410step0Labels = raw410Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw410 raw410Labels permutation152 permutation5
    mixedMoment B raw410step0 raw410step0Labels = mixedMoment B raw410step1 raw410step1Labels := by
      have ha : raw410step1 = raw410step0 := by apply Matrix.ext; unfold raw410step1 raw410step0; decide +kernel
      have hl : raw410step0Labels = labelEmbedding1 ∘ raw410step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw410step0 raw410step0Labels raw410step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3140 node3140Labels := by rfl

def raw411 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw411Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw411step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw411 raw411Labels = mixedMoment B node171 node171Labels := by
  calc
    mixedMoment B raw411 raw411Labels = mixedMoment B raw411step0 raw411step0Labels := by
      have ha : raw411step0 = (fun i j => raw411 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw411step0 raw411; decide +kernel
      have hl : raw411step0Labels = raw411Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw411 raw411Labels permutation160 permutation4
    _ = mixedMoment B node171 node171Labels := by rfl

def raw412 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw412step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw412 raw412Labels = mixedMoment B node3141 node3141Labels := by
  calc
    mixedMoment B raw412 raw412Labels = mixedMoment B raw412step0 raw412step0Labels := by
      have ha : raw412step0 = (fun i j => raw412 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw412step0 raw412; decide +kernel
      have hl : raw412step0Labels = raw412Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw412 raw412Labels permutation32 permutation5
    mixedMoment B raw412step0 raw412step0Labels = mixedMoment B raw412step1 raw412step1Labels := by
      have ha : raw412step1 = raw412step0 := by apply Matrix.ext; unfold raw412step1 raw412step0; decide +kernel
      have hl : raw412step0Labels = labelEmbedding1 ∘ raw412step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw412step0 raw412step0Labels raw412step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3141 node3141Labels := by rfl

def raw413 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw413Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw413step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw413 raw413Labels = mixedMoment B node182 node182Labels := by
  calc
    mixedMoment B raw413 raw413Labels = mixedMoment B raw413step0 raw413step0Labels := by
      have ha : raw413step0 = (fun i j => raw413 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw413step0 raw413; decide +kernel
      have hl : raw413step0Labels = raw413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw413 raw413Labels permutation33 permutation4
    _ = mixedMoment B node182 node182Labels := by rfl

def raw414 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw414 raw414Labels = mixedMoment B node3142 node3142Labels := by
  calc
    mixedMoment B raw414 raw414Labels = mixedMoment B raw414step0 raw414step0Labels := by
      have ha : raw414step0 = (fun i j => raw414 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw414step0 raw414; decide +kernel
      have hl : raw414step0Labels = raw414Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw414 raw414Labels permutation32 permutation5
    mixedMoment B raw414step0 raw414step0Labels = mixedMoment B raw414step1 raw414step1Labels := by
      have ha : raw414step1 = raw414step0 := by apply Matrix.ext; unfold raw414step1 raw414step0; decide +kernel
      have hl : raw414step0Labels = labelEmbedding1 ∘ raw414step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw414step0 raw414step0Labels raw414step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3142 node3142Labels := by rfl

def raw415 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw415Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw415step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw415 raw415Labels = mixedMoment B node183 node183Labels := by
  calc
    mixedMoment B raw415 raw415Labels = mixedMoment B raw415step0 raw415step0Labels := by
      have ha : raw415step0 = (fun i j => raw415 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw415step0 raw415; decide +kernel
      have hl : raw415step0Labels = raw415Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw415 raw415Labels permutation32 permutation4
    _ = mixedMoment B node183 node183Labels := by rfl

def raw416 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw416step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw416 raw416Labels = mixedMoment B node3143 node3143Labels := by
  calc
    mixedMoment B raw416 raw416Labels = mixedMoment B raw416step0 raw416step0Labels := by
      have ha : raw416step0 = (fun i j => raw416 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw416step0 raw416; decide +kernel
      have hl : raw416step0Labels = raw416Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw416 raw416Labels permutation32 permutation5
    mixedMoment B raw416step0 raw416step0Labels = mixedMoment B raw416step1 raw416step1Labels := by
      have ha : raw416step1 = raw416step0 := by apply Matrix.ext; unfold raw416step1 raw416step0; decide +kernel
      have hl : raw416step0Labels = labelEmbedding1 ∘ raw416step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw416step0 raw416step0Labels raw416step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3143 node3143Labels := by rfl

def raw417 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw417Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw417step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw417 raw417Labels = mixedMoment B node173 node173Labels := by
  calc
    mixedMoment B raw417 raw417Labels = mixedMoment B raw417step0 raw417step0Labels := by
      have ha : raw417step0 = (fun i j => raw417 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw417step0 raw417; decide +kernel
      have hl : raw417step0Labels = raw417Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw417 raw417Labels permutation32 permutation4
    _ = mixedMoment B node173 node173Labels := by rfl

def raw418 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw418step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw418 raw418Labels = mixedMoment B node3144 node3144Labels := by
  calc
    mixedMoment B raw418 raw418Labels = mixedMoment B raw418step0 raw418step0Labels := by
      have ha : raw418step0 = (fun i j => raw418 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw418step0 raw418; decide +kernel
      have hl : raw418step0Labels = raw418Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw418 raw418Labels permutation32 permutation5
    mixedMoment B raw418step0 raw418step0Labels = mixedMoment B raw418step1 raw418step1Labels := by
      have ha : raw418step1 = raw418step0 := by apply Matrix.ext; unfold raw418step1 raw418step0; decide +kernel
      have hl : raw418step0Labels = labelEmbedding1 ∘ raw418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw418step0 raw418step0Labels raw418step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3144 node3144Labels := by rfl

def raw419 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw419Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw419step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw419 raw419Labels = mixedMoment B node178 node178Labels := by
  calc
    mixedMoment B raw419 raw419Labels = mixedMoment B raw419step0 raw419step0Labels := by
      have ha : raw419step0 = (fun i j => raw419 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw419step0 raw419; decide +kernel
      have hl : raw419step0Labels = raw419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw419 raw419Labels permutation33 permutation4
    _ = mixedMoment B node178 node178Labels := by rfl

def raw420 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw420step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, 0, -2], ![3, -3, 0]]
def raw420step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, 0, -2], ![3, -3, 0]]
def raw420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw420 raw420Labels = mixedMoment B node3145 node3145Labels := by
  calc
    mixedMoment B raw420 raw420Labels = mixedMoment B raw420step0 raw420step0Labels := by
      have ha : raw420step0 = (fun i j => raw420 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw420step0 raw420; decide +kernel
      have hl : raw420step0Labels = raw420Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw420 raw420Labels permutation8 permutation5
    mixedMoment B raw420step0 raw420step0Labels = mixedMoment B raw420step1 raw420step1Labels := by
      have ha : raw420step1 = raw420step0 := by apply Matrix.ext; unfold raw420step1 raw420step0; decide +kernel
      have hl : raw420step0Labels = labelEmbedding1 ∘ raw420step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw420step0 raw420step0Labels raw420step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3145 node3145Labels := by rfl

def raw421 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw421Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw421step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw421step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw421 raw421Labels = mixedMoment B node185 node185Labels := by
  calc
    mixedMoment B raw421 raw421Labels = mixedMoment B raw421step0 raw421step0Labels := by
      have ha : raw421step0 = (fun i j => raw421 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw421step0 raw421; decide +kernel
      have hl : raw421step0Labels = raw421Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw421 raw421Labels permutation8 permutation4
    _ = mixedMoment B node185 node185Labels := by rfl

def raw422 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw422step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw422 raw422Labels = mixedMoment B node3177 node3177Labels := by
  calc
    mixedMoment B raw422 raw422Labels = mixedMoment B raw422step0 raw422step0Labels := by
      have ha : raw422step0 = (fun i j => raw422 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw422step0 raw422; decide +kernel
      have hl : raw422step0Labels = raw422Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw422 raw422Labels permutation32 permutation5
    mixedMoment B raw422step0 raw422step0Labels = mixedMoment B raw422step1 raw422step1Labels := by
      have ha : raw422step1 = raw422step0 := by apply Matrix.ext; unfold raw422step1 raw422step0; decide +kernel
      have hl : raw422step0Labels = labelEmbedding1 ∘ raw422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw422step0 raw422step0Labels raw422step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3177 node3177Labels := by rfl

def raw423 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw423Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw423step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw423step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw423 raw423Labels = mixedMoment B node219 node219Labels := by
  calc
    mixedMoment B raw423 raw423Labels = mixedMoment B raw423step0 raw423step0Labels := by
      have ha : raw423step0 = (fun i j => raw423 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw423step0 raw423; decide +kernel
      have hl : raw423step0Labels = raw423Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw423 raw423Labels permutation151 permutation4
    mixedMoment B raw423step0 raw423step0Labels = mixedMoment B raw423step1 raw423step1Labels := by
      have ha : raw423step1 = -raw423step0 := by apply Matrix.ext; change ∀ i j, raw423step1 i j = -(raw423step0 i j); unfold raw423step1 raw423step0; decide +kernel
      have hl : raw423step1Labels = raw423step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node219 node219Labels := by rfl

def raw424 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw424 raw424Labels = mixedMoment B node3178 node3178Labels := by
  calc
    mixedMoment B raw424 raw424Labels = mixedMoment B raw424step0 raw424step0Labels := by
      have ha : raw424step0 = (fun i j => raw424 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw424step0 raw424; decide +kernel
      have hl : raw424step0Labels = raw424Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw424 raw424Labels permutation32 permutation5
    mixedMoment B raw424step0 raw424step0Labels = mixedMoment B raw424step1 raw424step1Labels := by
      have ha : raw424step1 = raw424step0 := by apply Matrix.ext; unfold raw424step1 raw424step0; decide +kernel
      have hl : raw424step0Labels = labelEmbedding1 ∘ raw424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw424step0 raw424step0Labels raw424step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3178 node3178Labels := by rfl

def raw425 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw425Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw425step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw425step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw425 raw425Labels = mixedMoment B node231 node231Labels := by
  calc
    mixedMoment B raw425 raw425Labels = mixedMoment B raw425step0 raw425step0Labels := by
      have ha : raw425step0 = (fun i j => raw425 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw425step0 raw425; decide +kernel
      have hl : raw425step0Labels = raw425Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw425 raw425Labels permutation39 permutation6
    mixedMoment B raw425step0 raw425step0Labels = mixedMoment B raw425step1 raw425step1Labels := by
      have ha : raw425step1 = -raw425step0 := by apply Matrix.ext; change ∀ i j, raw425step1 i j = -(raw425step0 i j); unfold raw425step1 raw425step0; decide +kernel
      have hl : raw425step1Labels = raw425step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node231 node231Labels := by rfl

def raw426 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw426step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw426 raw426Labels = mixedMoment B node3182 node3182Labels := by
  calc
    mixedMoment B raw426 raw426Labels = mixedMoment B raw426step0 raw426step0Labels := by
      have ha : raw426step0 = (fun i j => raw426 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw426step0 raw426; decide +kernel
      have hl : raw426step0Labels = raw426Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw426 raw426Labels permutation152 permutation5
    mixedMoment B raw426step0 raw426step0Labels = mixedMoment B raw426step1 raw426step1Labels := by
      have ha : raw426step1 = raw426step0 := by apply Matrix.ext; unfold raw426step1 raw426step0; decide +kernel
      have hl : raw426step0Labels = labelEmbedding1 ∘ raw426step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw426step0 raw426step0Labels raw426step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3182 node3182Labels := by rfl

def raw427 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw427Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw427step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw427 raw427Labels = mixedMoment B node243 node243Labels := by
  calc
    mixedMoment B raw427 raw427Labels = mixedMoment B raw427step0 raw427step0Labels := by
      have ha : raw427step0 = (fun i j => raw427 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw427step0 raw427; decide +kernel
      have hl : raw427step0Labels = raw427Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw427 raw427Labels permutation168 permutation4
    _ = mixedMoment B node243 node243Labels := by rfl

def raw428 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw428step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw428 raw428Labels = mixedMoment B node3183 node3183Labels := by
  calc
    mixedMoment B raw428 raw428Labels = mixedMoment B raw428step0 raw428step0Labels := by
      have ha : raw428step0 = (fun i j => raw428 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw428step0 raw428; decide +kernel
      have hl : raw428step0Labels = raw428Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw428 raw428Labels permutation32 permutation5
    mixedMoment B raw428step0 raw428step0Labels = mixedMoment B raw428step1 raw428step1Labels := by
      have ha : raw428step1 = raw428step0 := by apply Matrix.ext; unfold raw428step1 raw428step0; decide +kernel
      have hl : raw428step0Labels = labelEmbedding1 ∘ raw428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw428step0 raw428step0Labels raw428step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3183 node3183Labels := by rfl

def raw429 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw429Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw429step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw429 raw429Labels = mixedMoment B node248 node248Labels := by
  calc
    mixedMoment B raw429 raw429Labels = mixedMoment B raw429step0 raw429step0Labels := by
      have ha : raw429step0 = (fun i j => raw429 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw429step0 raw429; decide +kernel
      have hl : raw429step0Labels = raw429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw429 raw429Labels permutation32 permutation4
    _ = mixedMoment B node248 node248Labels := by rfl

def raw430 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw430step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw430 raw430Labels = mixedMoment B node3184 node3184Labels := by
  calc
    mixedMoment B raw430 raw430Labels = mixedMoment B raw430step0 raw430step0Labels := by
      have ha : raw430step0 = (fun i j => raw430 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw430step0 raw430; decide +kernel
      have hl : raw430step0Labels = raw430Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw430 raw430Labels permutation32 permutation5
    mixedMoment B raw430step0 raw430step0Labels = mixedMoment B raw430step1 raw430step1Labels := by
      have ha : raw430step1 = raw430step0 := by apply Matrix.ext; unfold raw430step1 raw430step0; decide +kernel
      have hl : raw430step0Labels = labelEmbedding1 ∘ raw430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw430step0 raw430step0Labels raw430step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3184 node3184Labels := by rfl

def raw431 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw431Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw431step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw431 raw431Labels = mixedMoment B node245 node245Labels := by
  calc
    mixedMoment B raw431 raw431Labels = mixedMoment B raw431step0 raw431step0Labels := by
      have ha : raw431step0 = (fun i j => raw431 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw431step0 raw431; decide +kernel
      have hl : raw431step0Labels = raw431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw431 raw431Labels permutation34 permutation4
    _ = mixedMoment B node245 node245Labels := by rfl

def raw432 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw432step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw432 raw432Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw432 raw432Labels = mixedMoment B raw432step0 raw432step0Labels := by
      have ha : raw432step0 = (fun i j => raw432 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw432step0 raw432; decide +kernel
      have hl : raw432step0Labels = raw432Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw432 raw432Labels permutation32 permutation5
    mixedMoment B raw432step0 raw432step0Labels = mixedMoment B raw432step1 raw432step1Labels := by
      have ha : raw432step1 = raw432step0 := by apply Matrix.ext; unfold raw432step1 raw432step0; decide +kernel
      have hl : raw432step0Labels = labelEmbedding1 ∘ raw432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw432step0 raw432step0Labels raw432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw433 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw433Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw433step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw433 raw433Labels = mixedMoment B node244 node244Labels := by
  calc
    mixedMoment B raw433 raw433Labels = mixedMoment B raw433step0 raw433step0Labels := by
      have ha : raw433step0 = (fun i j => raw433 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw433step0 raw433; decide +kernel
      have hl : raw433step0Labels = raw433Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw433 raw433Labels permutation32 permutation4
    _ = mixedMoment B node244 node244Labels := by rfl

def raw434 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw434step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -3, 0]]
def raw434step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -3, 0]]
def raw434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw434 raw434Labels = mixedMoment B node3186 node3186Labels := by
  calc
    mixedMoment B raw434 raw434Labels = mixedMoment B raw434step0 raw434step0Labels := by
      have ha : raw434step0 = (fun i j => raw434 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw434step0 raw434; decide +kernel
      have hl : raw434step0Labels = raw434Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw434 raw434Labels permutation8 permutation5
    mixedMoment B raw434step0 raw434step0Labels = mixedMoment B raw434step1 raw434step1Labels := by
      have ha : raw434step1 = raw434step0 := by apply Matrix.ext; unfold raw434step1 raw434step0; decide +kernel
      have hl : raw434step0Labels = labelEmbedding1 ∘ raw434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw434step0 raw434step0Labels raw434step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3186 node3186Labels := by rfl

def raw435 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw435Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw435step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw435step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw435 raw435Labels = mixedMoment B node241 node241Labels := by
  calc
    mixedMoment B raw435 raw435Labels = mixedMoment B raw435step0 raw435step0Labels := by
      have ha : raw435step0 = (fun i j => raw435 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw435step0 raw435; decide +kernel
      have hl : raw435step0Labels = raw435Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw435 raw435Labels permutation8 permutation4
    _ = mixedMoment B node241 node241Labels := by rfl

def raw436 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw436step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw436step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw436 raw436Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw436 raw436Labels = mixedMoment B raw436step0 raw436step0Labels := by
      have ha : raw436step0 = (fun i j => raw436 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw436step0 raw436; decide +kernel
      have hl : raw436step0Labels = raw436Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw436 raw436Labels permutation8 permutation5
    mixedMoment B raw436step0 raw436step0Labels = mixedMoment B raw436step1 raw436step1Labels := by
      have ha : raw436step1 = raw436step0 := by apply Matrix.ext; unfold raw436step1 raw436step0; decide +kernel
      have hl : raw436step0Labels = labelEmbedding1 ∘ raw436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw436step0 raw436step0Labels raw436step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3187 node3187Labels := by rfl

def raw437 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw437Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw437step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw437step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw437 raw437Labels = mixedMoment B node251 node251Labels := by
  calc
    mixedMoment B raw437 raw437Labels = mixedMoment B raw437step0 raw437step0Labels := by
      have ha : raw437step0 = (fun i j => raw437 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw437step0 raw437; decide +kernel
      have hl : raw437step0Labels = raw437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw437 raw437Labels permutation9 permutation4
    _ = mixedMoment B node251 node251Labels := by rfl

def raw438 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw438step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw438step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw438 raw438Labels = mixedMoment B node3188 node3188Labels := by
  calc
    mixedMoment B raw438 raw438Labels = mixedMoment B raw438step0 raw438step0Labels := by
      have ha : raw438step0 = (fun i j => raw438 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw438step0 raw438; decide +kernel
      have hl : raw438step0Labels = raw438Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw438 raw438Labels permutation8 permutation5
    mixedMoment B raw438step0 raw438step0Labels = mixedMoment B raw438step1 raw438step1Labels := by
      have ha : raw438step1 = raw438step0 := by apply Matrix.ext; unfold raw438step1 raw438step0; decide +kernel
      have hl : raw438step0Labels = labelEmbedding1 ∘ raw438step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw438step0 raw438step0Labels raw438step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3188 node3188Labels := by rfl

def raw439 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw439Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw439step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw439step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw439 raw439Labels = mixedMoment B node252 node252Labels := by
  calc
    mixedMoment B raw439 raw439Labels = mixedMoment B raw439step0 raw439step0Labels := by
      have ha : raw439step0 = (fun i j => raw439 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw439step0 raw439; decide +kernel
      have hl : raw439step0Labels = raw439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw439 raw439Labels permutation8 permutation4
    _ = mixedMoment B node252 node252Labels := by rfl

def raw440 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw440step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw440 raw440Labels = mixedMoment B node3190 node3190Labels := by
  calc
    mixedMoment B raw440 raw440Labels = mixedMoment B raw440step0 raw440step0Labels := by
      have ha : raw440step0 = (fun i j => raw440 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw440step0 raw440; decide +kernel
      have hl : raw440step0Labels = raw440Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw440 raw440Labels permutation152 permutation5
    mixedMoment B raw440step0 raw440step0Labels = mixedMoment B raw440step1 raw440step1Labels := by
      have ha : raw440step1 = raw440step0 := by apply Matrix.ext; unfold raw440step1 raw440step0; decide +kernel
      have hl : raw440step0Labels = labelEmbedding1 ∘ raw440step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw440step0 raw440step0Labels raw440step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3190 node3190Labels := by rfl

def raw441 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw441Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw441step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw441 raw441Labels = mixedMoment B node209 node209Labels := by
  calc
    mixedMoment B raw441 raw441Labels = mixedMoment B raw441step0 raw441step0Labels := by
      have ha : raw441step0 = (fun i j => raw441 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw441step0 raw441; decide +kernel
      have hl : raw441step0Labels = raw441Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw441 raw441Labels permutation153 permutation4
    _ = mixedMoment B node209 node209Labels := by rfl

def raw442 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw442 raw442Labels = mixedMoment B node3191 node3191Labels := by
  calc
    mixedMoment B raw442 raw442Labels = mixedMoment B raw442step0 raw442step0Labels := by
      have ha : raw442step0 = (fun i j => raw442 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw442step0 raw442; decide +kernel
      have hl : raw442step0Labels = raw442Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw442 raw442Labels permutation152 permutation5
    mixedMoment B raw442step0 raw442step0Labels = mixedMoment B raw442step1 raw442step1Labels := by
      have ha : raw442step1 = raw442step0 := by apply Matrix.ext; unfold raw442step1 raw442step0; decide +kernel
      have hl : raw442step0Labels = labelEmbedding1 ∘ raw442step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw442step0 raw442step0Labels raw442step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3191 node3191Labels := by rfl

def raw443 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw443Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw443step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw443 raw443Labels = mixedMoment B node210 node210Labels := by
  calc
    mixedMoment B raw443 raw443Labels = mixedMoment B raw443step0 raw443step0Labels := by
      have ha : raw443step0 = (fun i j => raw443 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw443step0 raw443; decide +kernel
      have hl : raw443step0Labels = raw443Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw443 raw443Labels permutation152 permutation4
    _ = mixedMoment B node210 node210Labels := by rfl

def raw444 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw444step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw444 raw444Labels = mixedMoment B node3192 node3192Labels := by
  calc
    mixedMoment B raw444 raw444Labels = mixedMoment B raw444step0 raw444step0Labels := by
      have ha : raw444step0 = (fun i j => raw444 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw444step0 raw444; decide +kernel
      have hl : raw444step0Labels = raw444Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw444 raw444Labels permutation152 permutation5
    mixedMoment B raw444step0 raw444step0Labels = mixedMoment B raw444step1 raw444step1Labels := by
      have ha : raw444step1 = raw444step0 := by apply Matrix.ext; unfold raw444step1 raw444step0; decide +kernel
      have hl : raw444step0Labels = labelEmbedding1 ∘ raw444step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw444step0 raw444step0Labels raw444step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3192 node3192Labels := by rfl

def raw445 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw445Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw445step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw445 raw445Labels = mixedMoment B node205 node205Labels := by
  calc
    mixedMoment B raw445 raw445Labels = mixedMoment B raw445step0 raw445step0Labels := by
      have ha : raw445step0 = (fun i j => raw445 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw445step0 raw445; decide +kernel
      have hl : raw445step0Labels = raw445Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw445 raw445Labels permutation152 permutation4
    _ = mixedMoment B node205 node205Labels := by rfl

def raw446 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw446step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw446 raw446Labels = mixedMoment B node3200 node3200Labels := by
  calc
    mixedMoment B raw446 raw446Labels = mixedMoment B raw446step0 raw446step0Labels := by
      have ha : raw446step0 = (fun i j => raw446 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw446step0 raw446; decide +kernel
      have hl : raw446step0Labels = raw446Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw446 raw446Labels permutation152 permutation5
    mixedMoment B raw446step0 raw446step0Labels = mixedMoment B raw446step1 raw446step1Labels := by
      have ha : raw446step1 = raw446step0 := by apply Matrix.ext; unfold raw446step1 raw446step0; decide +kernel
      have hl : raw446step0Labels = labelEmbedding1 ∘ raw446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw446step0 raw446step0Labels raw446step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3200 node3200Labels := by rfl

def raw447 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw447Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw447step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw447 raw447Labels = mixedMoment B node215 node215Labels := by
  calc
    mixedMoment B raw447 raw447Labels = mixedMoment B raw447step0 raw447step0Labels := by
      have ha : raw447step0 = (fun i j => raw447 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw447step0 raw447; decide +kernel
      have hl : raw447step0Labels = raw447Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw447 raw447Labels permutation158 permutation4
    _ = mixedMoment B node215 node215Labels := by rfl

def raw448 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw448step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw448 raw448Labels = mixedMoment B node3201 node3201Labels := by
  calc
    mixedMoment B raw448 raw448Labels = mixedMoment B raw448step0 raw448step0Labels := by
      have ha : raw448step0 = (fun i j => raw448 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw448step0 raw448; decide +kernel
      have hl : raw448step0Labels = raw448Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw448 raw448Labels permutation152 permutation5
    mixedMoment B raw448step0 raw448step0Labels = mixedMoment B raw448step1 raw448step1Labels := by
      have ha : raw448step1 = raw448step0 := by apply Matrix.ext; unfold raw448step1 raw448step0; decide +kernel
      have hl : raw448step0Labels = labelEmbedding1 ∘ raw448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw448step0 raw448step0Labels raw448step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3201 node3201Labels := by rfl

def raw449 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw449Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw449step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw449 raw449Labels = mixedMoment B node217 node217Labels := by
  calc
    mixedMoment B raw449 raw449Labels = mixedMoment B raw449step0 raw449step0Labels := by
      have ha : raw449step0 = (fun i j => raw449 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw449step0 raw449; decide +kernel
      have hl : raw449step0Labels = raw449Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw449 raw449Labels permutation159 permutation4
    _ = mixedMoment B node217 node217Labels := by rfl

def raw450 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw450step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw450 raw450Labels = mixedMoment B node3203 node3203Labels := by
  calc
    mixedMoment B raw450 raw450Labels = mixedMoment B raw450step0 raw450step0Labels := by
      have ha : raw450step0 = (fun i j => raw450 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw450step0 raw450; decide +kernel
      have hl : raw450step0Labels = raw450Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw450 raw450Labels permutation152 permutation5
    mixedMoment B raw450step0 raw450step0Labels = mixedMoment B raw450step1 raw450step1Labels := by
      have ha : raw450step1 = raw450step0 := by apply Matrix.ext; unfold raw450step1 raw450step0; decide +kernel
      have hl : raw450step0Labels = labelEmbedding1 ∘ raw450step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw450step0 raw450step0Labels raw450step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3203 node3203Labels := by rfl

def raw451 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw451Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw451step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw451 raw451Labels = mixedMoment B node223 node223Labels := by
  calc
    mixedMoment B raw451 raw451Labels = mixedMoment B raw451step0 raw451step0Labels := by
      have ha : raw451step0 = (fun i j => raw451 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw451step0 raw451; decide +kernel
      have hl : raw451step0Labels = raw451Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw451 raw451Labels permutation152 permutation4
    _ = mixedMoment B node223 node223Labels := by rfl

def raw452 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw452step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw452 raw452Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw452 raw452Labels = mixedMoment B raw452step0 raw452step0Labels := by
      have ha : raw452step0 = (fun i j => raw452 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw452step0 raw452; decide +kernel
      have hl : raw452step0Labels = raw452Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw452 raw452Labels permutation152 permutation5
    mixedMoment B raw452step0 raw452step0Labels = mixedMoment B raw452step1 raw452step1Labels := by
      have ha : raw452step1 = raw452step0 := by apply Matrix.ext; unfold raw452step1 raw452step0; decide +kernel
      have hl : raw452step0Labels = labelEmbedding1 ∘ raw452step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw452step0 raw452step0Labels raw452step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3204 node3204Labels := by rfl

def raw453 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw453Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw453step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw453 raw453Labels = mixedMoment B node221 node221Labels := by
  calc
    mixedMoment B raw453 raw453Labels = mixedMoment B raw453step0 raw453step0Labels := by
      have ha : raw453step0 = (fun i j => raw453 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw453step0 raw453; decide +kernel
      have hl : raw453step0Labels = raw453Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw453 raw453Labels permutation154 permutation4
    _ = mixedMoment B node221 node221Labels := by rfl

def raw454 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw454 raw454Labels = mixedMoment B node3205 node3205Labels := by
  calc
    mixedMoment B raw454 raw454Labels = mixedMoment B raw454step0 raw454step0Labels := by
      have ha : raw454step0 = (fun i j => raw454 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw454step0 raw454; decide +kernel
      have hl : raw454step0Labels = raw454Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw454 raw454Labels permutation152 permutation5
    mixedMoment B raw454step0 raw454step0Labels = mixedMoment B raw454step1 raw454step1Labels := by
      have ha : raw454step1 = raw454step0 := by apply Matrix.ext; unfold raw454step1 raw454step0; decide +kernel
      have hl : raw454step0Labels = labelEmbedding1 ∘ raw454step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw454step0 raw454step0Labels raw454step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3205 node3205Labels := by rfl

def raw455 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw455Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw455step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw455 raw455Labels = mixedMoment B node220 node220Labels := by
  calc
    mixedMoment B raw455 raw455Labels = mixedMoment B raw455step0 raw455step0Labels := by
      have ha : raw455step0 = (fun i j => raw455 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw455step0 raw455; decide +kernel
      have hl : raw455step0Labels = raw455Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw455 raw455Labels permutation152 permutation4
    _ = mixedMoment B node220 node220Labels := by rfl

def raw456 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw456step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw456 raw456Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw456 raw456Labels = mixedMoment B raw456step0 raw456step0Labels := by
      have ha : raw456step0 = (fun i j => raw456 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw456step0 raw456; decide +kernel
      have hl : raw456step0Labels = raw456Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw456 raw456Labels permutation32 permutation5
    mixedMoment B raw456step0 raw456step0Labels = mixedMoment B raw456step1 raw456step1Labels := by
      have ha : raw456step1 = raw456step0 := by apply Matrix.ext; unfold raw456step1 raw456step0; decide +kernel
      have hl : raw456step0Labels = labelEmbedding1 ∘ raw456step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw456step0 raw456step0Labels raw456step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw457 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw457Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw457step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw457 raw457Labels = mixedMoment B node226 node226Labels := by
  calc
    mixedMoment B raw457 raw457Labels = mixedMoment B raw457step0 raw457step0Labels := by
      have ha : raw457step0 = (fun i j => raw457 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw457step0 raw457; decide +kernel
      have hl : raw457step0Labels = raw457Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw457 raw457Labels permutation33 permutation4
    _ = mixedMoment B node226 node226Labels := by rfl

def raw458 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw458step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw458 raw458Labels = mixedMoment B node3207 node3207Labels := by
  calc
    mixedMoment B raw458 raw458Labels = mixedMoment B raw458step0 raw458step0Labels := by
      have ha : raw458step0 = (fun i j => raw458 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw458step0 raw458; decide +kernel
      have hl : raw458step0Labels = raw458Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw458 raw458Labels permutation32 permutation5
    mixedMoment B raw458step0 raw458step0Labels = mixedMoment B raw458step1 raw458step1Labels := by
      have ha : raw458step1 = raw458step0 := by apply Matrix.ext; unfold raw458step1 raw458step0; decide +kernel
      have hl : raw458step0Labels = labelEmbedding1 ∘ raw458step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw458step0 raw458step0Labels raw458step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3207 node3207Labels := by rfl

def raw459 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw459Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw459step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw459 raw459Labels = mixedMoment B node227 node227Labels := by
  calc
    mixedMoment B raw459 raw459Labels = mixedMoment B raw459step0 raw459step0Labels := by
      have ha : raw459step0 = (fun i j => raw459 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw459step0 raw459; decide +kernel
      have hl : raw459step0Labels = raw459Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw459 raw459Labels permutation32 permutation4
    _ = mixedMoment B node227 node227Labels := by rfl

def raw460 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw460step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw460 raw460Labels = mixedMoment B node3209 node3209Labels := by
  calc
    mixedMoment B raw460 raw460Labels = mixedMoment B raw460step0 raw460step0Labels := by
      have ha : raw460step0 = (fun i j => raw460 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw460step0 raw460; decide +kernel
      have hl : raw460step0Labels = raw460Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw460 raw460Labels permutation152 permutation5
    mixedMoment B raw460step0 raw460step0Labels = mixedMoment B raw460step1 raw460step1Labels := by
      have ha : raw460step1 = raw460step0 := by apply Matrix.ext; unfold raw460step1 raw460step0; decide +kernel
      have hl : raw460step0Labels = labelEmbedding1 ∘ raw460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw460step0 raw460step0Labels raw460step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3209 node3209Labels := by rfl

def raw461 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw461Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw461step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw461 raw461Labels = mixedMoment B node232 node232Labels := by
  calc
    mixedMoment B raw461 raw461Labels = mixedMoment B raw461step0 raw461step0Labels := by
      have ha : raw461step0 = (fun i j => raw461 (permutation169 i) (permutation4 j)) := by apply Matrix.ext; unfold raw461step0 raw461; decide +kernel
      have hl : raw461step0Labels = raw461Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw461 raw461Labels permutation169 permutation4
    _ = mixedMoment B node232 node232Labels := by rfl

def raw462 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw462 raw462Labels = mixedMoment B node3210 node3210Labels := by
  calc
    mixedMoment B raw462 raw462Labels = mixedMoment B raw462step0 raw462step0Labels := by
      have ha : raw462step0 = (fun i j => raw462 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw462step0 raw462; decide +kernel
      have hl : raw462step0Labels = raw462Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw462 raw462Labels permutation32 permutation5
    mixedMoment B raw462step0 raw462step0Labels = mixedMoment B raw462step1 raw462step1Labels := by
      have ha : raw462step1 = raw462step0 := by apply Matrix.ext; unfold raw462step1 raw462step0; decide +kernel
      have hl : raw462step0Labels = labelEmbedding1 ∘ raw462step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw462step0 raw462step0Labels raw462step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3210 node3210Labels := by rfl

def raw463 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw463Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw463step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw463 raw463Labels = mixedMoment B node235 node235Labels := by
  calc
    mixedMoment B raw463 raw463Labels = mixedMoment B raw463step0 raw463step0Labels := by
      have ha : raw463step0 = (fun i j => raw463 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw463step0 raw463; decide +kernel
      have hl : raw463step0Labels = raw463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw463 raw463Labels permutation34 permutation4
    _ = mixedMoment B node235 node235Labels := by rfl

def raw464 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw464step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw464 raw464Labels = mixedMoment B node3211 node3211Labels := by
  calc
    mixedMoment B raw464 raw464Labels = mixedMoment B raw464step0 raw464step0Labels := by
      have ha : raw464step0 = (fun i j => raw464 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw464step0 raw464; decide +kernel
      have hl : raw464step0Labels = raw464Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw464 raw464Labels permutation32 permutation5
    mixedMoment B raw464step0 raw464step0Labels = mixedMoment B raw464step1 raw464step1Labels := by
      have ha : raw464step1 = raw464step0 := by apply Matrix.ext; unfold raw464step1 raw464step0; decide +kernel
      have hl : raw464step0Labels = labelEmbedding1 ∘ raw464step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw464step0 raw464step0Labels raw464step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3211 node3211Labels := by rfl

def raw465 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw465Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw465step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw465 raw465Labels = mixedMoment B node234 node234Labels := by
  calc
    mixedMoment B raw465 raw465Labels = mixedMoment B raw465step0 raw465step0Labels := by
      have ha : raw465step0 = (fun i j => raw465 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw465step0 raw465; decide +kernel
      have hl : raw465step0Labels = raw465Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw465 raw465Labels permutation34 permutation4
    _ = mixedMoment B node234 node234Labels := by rfl

def raw466 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw466Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw466step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw466 raw466Labels = mixedMoment B node3218 node3218Labels := by
  calc
    mixedMoment B raw466 raw466Labels = mixedMoment B raw466step0 raw466step0Labels := by
      have ha : raw466step0 = (fun i j => raw466 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw466step0 raw466; decide +kernel
      have hl : raw466step0Labels = raw466Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw466 raw466Labels permutation152 permutation5
    mixedMoment B raw466step0 raw466step0Labels = mixedMoment B raw466step1 raw466step1Labels := by
      have ha : raw466step1 = raw466step0 := by apply Matrix.ext; unfold raw466step1 raw466step0; decide +kernel
      have hl : raw466step0Labels = labelEmbedding1 ∘ raw466step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw466step0 raw466step0Labels raw466step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3218 node3218Labels := by rfl

def raw467 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw467Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw467step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw467step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw467 raw467Labels = mixedMoment B node200 node200Labels := by
  calc
    mixedMoment B raw467 raw467Labels = mixedMoment B raw467step0 raw467step0Labels := by
      have ha : raw467step0 = (fun i j => raw467 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw467step0 raw467; decide +kernel
      have hl : raw467step0Labels = raw467Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw467 raw467Labels permutation160 permutation6
    mixedMoment B raw467step0 raw467step0Labels = mixedMoment B raw467step1 raw467step1Labels := by
      have ha : raw467step1 = -raw467step0 := by apply Matrix.ext; change ∀ i j, raw467step1 i j = -(raw467step0 i j); unfold raw467step1 raw467step0; decide +kernel
      have hl : raw467step1Labels = raw467step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node200 node200Labels := by rfl

def raw468 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 2, -2], ![-2, 2, 0]]
def raw468Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw468step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw468 raw468Labels = mixedMoment B node3219 node3219Labels := by
  calc
    mixedMoment B raw468 raw468Labels = mixedMoment B raw468step0 raw468step0Labels := by
      have ha : raw468step0 = (fun i j => raw468 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw468step0 raw468; decide +kernel
      have hl : raw468step0Labels = raw468Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw468 raw468Labels permutation32 permutation5
    mixedMoment B raw468step0 raw468step0Labels = mixedMoment B raw468step1 raw468step1Labels := by
      have ha : raw468step1 = raw468step0 := by apply Matrix.ext; unfold raw468step1 raw468step0; decide +kernel
      have hl : raw468step0Labels = labelEmbedding1 ∘ raw468step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw468step0 raw468step0Labels raw468step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3219 node3219Labels := by rfl

def raw469 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 2, -2], ![-2, 2, 0]]
def raw469Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw469step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw469 raw469Labels = mixedMoment B node204 node204Labels := by
  calc
    mixedMoment B raw469 raw469Labels = mixedMoment B raw469step0 raw469step0Labels := by
      have ha : raw469step0 = (fun i j => raw469 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw469step0 raw469; decide +kernel
      have hl : raw469step0Labels = raw469Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw469 raw469Labels permutation33 permutation4
    _ = mixedMoment B node204 node204Labels := by rfl

def raw470 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw470step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw470 raw470Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw470 raw470Labels = mixedMoment B raw470step0 raw470step0Labels := by
      have ha : raw470step0 = (fun i j => raw470 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw470step0 raw470; decide +kernel
      have hl : raw470step0Labels = raw470Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw470 raw470Labels permutation32 permutation5
    mixedMoment B raw470step0 raw470step0Labels = mixedMoment B raw470step1 raw470step1Labels := by
      have ha : raw470step1 = raw470step0 := by apply Matrix.ext; unfold raw470step1 raw470step0; decide +kernel
      have hl : raw470step0Labels = labelEmbedding1 ∘ raw470step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw470step0 raw470step0Labels raw470step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw471 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw471Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw471step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw471step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw471 raw471Labels = mixedMoment B node261 node261Labels := by
  calc
    mixedMoment B raw471 raw471Labels = mixedMoment B raw471step0 raw471step0Labels := by
      have ha : raw471step0 = (fun i j => raw471 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw471step0 raw471; decide +kernel
      have hl : raw471step0Labels = raw471Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw471 raw471Labels permutation49 permutation6
    mixedMoment B raw471step0 raw471step0Labels = mixedMoment B raw471step1 raw471step1Labels := by
      have ha : raw471step1 = -raw471step0 := by apply Matrix.ext; change ∀ i j, raw471step1 i j = -(raw471step0 i j); unfold raw471step1 raw471step0; decide +kernel
      have hl : raw471step1Labels = raw471step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node261 node261Labels := by rfl

def raw472 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw472Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw472step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw472step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw472 raw472Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw472 raw472Labels = mixedMoment B raw472step0 raw472step0Labels := by
      have ha : raw472step0 = (fun i j => raw472 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw472step0 raw472; decide +kernel
      have hl : raw472step0Labels = raw472Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw472 raw472Labels permutation8 permutation5
    mixedMoment B raw472step0 raw472step0Labels = mixedMoment B raw472step1 raw472step1Labels := by
      have ha : raw472step1 = raw472step0 := by apply Matrix.ext; unfold raw472step1 raw472step0; decide +kernel
      have hl : raw472step0Labels = labelEmbedding1 ∘ raw472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw472step0 raw472step0Labels raw472step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

def raw473 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw473Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw473step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw473step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw473 raw473Labels = mixedMoment B node269 node269Labels := by
  calc
    mixedMoment B raw473 raw473Labels = mixedMoment B raw473step0 raw473step0Labels := by
      have ha : raw473step0 = (fun i j => raw473 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw473step0 raw473; decide +kernel
      have hl : raw473step0Labels = raw473Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw473 raw473Labels permutation8 permutation4
    _ = mixedMoment B node269 node269Labels := by rfl

def raw474 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw474Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw474step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw474 raw474Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw474 raw474Labels = mixedMoment B raw474step0 raw474step0Labels := by
      have ha : raw474step0 = (fun i j => raw474 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw474step0 raw474; decide +kernel
      have hl : raw474step0Labels = raw474Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw474 raw474Labels permutation8 permutation5
    mixedMoment B raw474step0 raw474step0Labels = mixedMoment B raw474step1 raw474step1Labels := by
      have ha : raw474step1 = raw474step0 := by apply Matrix.ext; unfold raw474step1 raw474step0; decide +kernel
      have hl : raw474step0Labels = labelEmbedding1 ∘ raw474step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw474step0 raw474step0Labels raw474step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw475 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw475Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw475step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw475step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw475step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw475 raw475Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw475 raw475Labels = mixedMoment B raw475step0 raw475step0Labels := by
      have ha : raw475step0 = (fun i j => raw475 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw475step0 raw475; decide +kernel
      have hl : raw475step0Labels = raw475Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw475 raw475Labels permutation11 permutation6
    mixedMoment B raw475step0 raw475step0Labels = mixedMoment B raw475step1 raw475step1Labels := by
      have ha : raw475step1 = -raw475step0 := by apply Matrix.ext; change ∀ i j, raw475step1 i j = -(raw475step0 i j); unfold raw475step1 raw475step0; decide +kernel
      have hl : raw475step1Labels = raw475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node268 node268Labels := by rfl

def raw476 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw476Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw476step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw476 raw476Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw476 raw476Labels = mixedMoment B raw476step0 raw476step0Labels := by
      have ha : raw476step0 = (fun i j => raw476 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw476step0 raw476; decide +kernel
      have hl : raw476step0Labels = raw476Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw476 raw476Labels permutation152 permutation5
    mixedMoment B raw476step0 raw476step0Labels = mixedMoment B raw476step1 raw476step1Labels := by
      have ha : raw476step1 = raw476step0 := by apply Matrix.ext; unfold raw476step1 raw476step0; decide +kernel
      have hl : raw476step0Labels = labelEmbedding1 ∘ raw476step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw476step0 raw476step0Labels raw476step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3226 node3226Labels := by rfl

def raw477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw477Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw477step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw477 raw477Labels = mixedMoment B node259 node259Labels := by
  calc
    mixedMoment B raw477 raw477Labels = mixedMoment B raw477step0 raw477step0Labels := by
      have ha : raw477step0 = (fun i j => raw477 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw477step0 raw477; decide +kernel
      have hl : raw477step0Labels = raw477Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw477 raw477Labels permutation155 permutation4
    _ = mixedMoment B node259 node259Labels := by rfl

def raw478 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw478Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw478step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw478 raw478Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw478 raw478Labels = mixedMoment B raw478step0 raw478step0Labels := by
      have ha : raw478step0 = (fun i j => raw478 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw478step0 raw478; decide +kernel
      have hl : raw478step0Labels = raw478Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw478 raw478Labels permutation32 permutation5
    mixedMoment B raw478step0 raw478step0Labels = mixedMoment B raw478step1 raw478step1Labels := by
      have ha : raw478step1 = raw478step0 := by apply Matrix.ext; unfold raw478step1 raw478step0; decide +kernel
      have hl : raw478step0Labels = labelEmbedding1 ∘ raw478step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw478step0 raw478step0Labels raw478step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw479 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw479Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw479step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw479 raw479Labels = mixedMoment B node260 node260Labels := by
  calc
    mixedMoment B raw479 raw479Labels = mixedMoment B raw479step0 raw479step0Labels := by
      have ha : raw479step0 = (fun i j => raw479 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw479step0 raw479; decide +kernel
      have hl : raw479step0Labels = raw479Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw479 raw479Labels permutation32 permutation4
    _ = mixedMoment B node260 node260Labels := by rfl

def raw480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw480Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw480 raw480Labels = mixedMoment B node3711 node3711Labels := by
  calc
    mixedMoment B raw480 raw480Labels = mixedMoment B raw480step0 raw480step0Labels := by
      have ha : raw480step0 = (fun i j => raw480 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw480step0 raw480; decide +kernel
      have hl : raw480step0Labels = raw480Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw480 raw480Labels permutation152 permutation5
    mixedMoment B raw480step0 raw480step0Labels = mixedMoment B raw480step1 raw480step1Labels := by
      have ha : raw480step1 = raw480step0 := by apply Matrix.ext; unfold raw480step1 raw480step0; decide +kernel
      have hl : raw480step0Labels = labelEmbedding1 ∘ raw480step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw480step0 raw480step0Labels raw480step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3711 node3711Labels := by rfl

def raw481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw481Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw481step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw481step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw481 raw481Labels = mixedMoment B node424 node424Labels := by
  calc
    mixedMoment B raw481 raw481Labels = mixedMoment B raw481step0 raw481step0Labels := by
      have ha : raw481step0 = (fun i j => raw481 (permutation588 i) (permutation4 j)) := by apply Matrix.ext; unfold raw481step0 raw481; decide +kernel
      have hl : raw481step0Labels = raw481Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw481 raw481Labels permutation588 permutation4
    mixedMoment B raw481step0 raw481step0Labels = mixedMoment B raw481step1 raw481step1Labels := by
      have ha : raw481step1 = -raw481step0 := by apply Matrix.ext; change ∀ i j, raw481step1 i j = -(raw481step0 i j); unfold raw481step1 raw481step0; decide +kernel
      have hl : raw481step1Labels = raw481step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node424 node424Labels := by rfl

def raw482 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw482Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw482step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw482 raw482Labels = mixedMoment B node3726 node3726Labels := by
  calc
    mixedMoment B raw482 raw482Labels = mixedMoment B raw482step0 raw482step0Labels := by
      have ha : raw482step0 = (fun i j => raw482 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw482step0 raw482; decide +kernel
      have hl : raw482step0Labels = raw482Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw482 raw482Labels permutation152 permutation5
    mixedMoment B raw482step0 raw482step0Labels = mixedMoment B raw482step1 raw482step1Labels := by
      have ha : raw482step1 = raw482step0 := by apply Matrix.ext; unfold raw482step1 raw482step0; decide +kernel
      have hl : raw482step0Labels = labelEmbedding1 ∘ raw482step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw482step0 raw482step0Labels raw482step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3726 node3726Labels := by rfl

def raw483 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw483Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw483step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw483 raw483Labels = mixedMoment B node442 node442Labels := by
  calc
    mixedMoment B raw483 raw483Labels = mixedMoment B raw483step0 raw483step0Labels := by
      have ha : raw483step0 = (fun i j => raw483 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw483step0 raw483; decide +kernel
      have hl : raw483step0Labels = raw483Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw483 raw483Labels permutation265 permutation4
    _ = mixedMoment B node442 node442Labels := by rfl

def raw484 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw484Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw484step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw484 raw484Labels = mixedMoment B node3727 node3727Labels := by
  calc
    mixedMoment B raw484 raw484Labels = mixedMoment B raw484step0 raw484step0Labels := by
      have ha : raw484step0 = (fun i j => raw484 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw484step0 raw484; decide +kernel
      have hl : raw484step0Labels = raw484Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw484 raw484Labels permutation152 permutation5
    mixedMoment B raw484step0 raw484step0Labels = mixedMoment B raw484step1 raw484step1Labels := by
      have ha : raw484step1 = raw484step0 := by apply Matrix.ext; unfold raw484step1 raw484step0; decide +kernel
      have hl : raw484step0Labels = labelEmbedding1 ∘ raw484step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw484step0 raw484step0Labels raw484step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3727 node3727Labels := by rfl

def raw485 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw485Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw485step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw485 raw485Labels = mixedMoment B node441 node441Labels := by
  calc
    mixedMoment B raw485 raw485Labels = mixedMoment B raw485step0 raw485step0Labels := by
      have ha : raw485step0 = (fun i j => raw485 (permutation267 i) (permutation4 j)) := by apply Matrix.ext; unfold raw485step0 raw485; decide +kernel
      have hl : raw485step0Labels = raw485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw485 raw485Labels permutation267 permutation4
    _ = mixedMoment B node441 node441Labels := by rfl

def raw486 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw486Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw486step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw486 raw486Labels = mixedMoment B node3728 node3728Labels := by
  calc
    mixedMoment B raw486 raw486Labels = mixedMoment B raw486step0 raw486step0Labels := by
      have ha : raw486step0 = (fun i j => raw486 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw486step0 raw486; decide +kernel
      have hl : raw486step0Labels = raw486Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw486 raw486Labels permutation32 permutation5
    mixedMoment B raw486step0 raw486step0Labels = mixedMoment B raw486step1 raw486step1Labels := by
      have ha : raw486step1 = raw486step0 := by apply Matrix.ext; unfold raw486step1 raw486step0; decide +kernel
      have hl : raw486step0Labels = labelEmbedding1 ∘ raw486step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw486step0 raw486step0Labels raw486step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3728 node3728Labels := by rfl

def raw487 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw487Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw487step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw487step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw487 raw487Labels = mixedMoment B node432 node432Labels := by
  calc
    mixedMoment B raw487 raw487Labels = mixedMoment B raw487step0 raw487step0Labels := by
      have ha : raw487step0 = (fun i j => raw487 (permutation126 i) (permutation4 j)) := by apply Matrix.ext; unfold raw487step0 raw487; decide +kernel
      have hl : raw487step0Labels = raw487Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw487 raw487Labels permutation126 permutation4
    mixedMoment B raw487step0 raw487step0Labels = mixedMoment B raw487step1 raw487step1Labels := by
      have ha : raw487step1 = -raw487step0 := by apply Matrix.ext; change ∀ i j, raw487step1 i j = -(raw487step0 i j); unfold raw487step1 raw487step0; decide +kernel
      have hl : raw487step1Labels = raw487step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node432 node432Labels := by rfl

def raw488 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw488Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw488step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw488 raw488Labels = mixedMoment B node3734 node3734Labels := by
  calc
    mixedMoment B raw488 raw488Labels = mixedMoment B raw488step0 raw488step0Labels := by
      have ha : raw488step0 = (fun i j => raw488 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw488step0 raw488; decide +kernel
      have hl : raw488step0Labels = raw488Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw488 raw488Labels permutation152 permutation5
    mixedMoment B raw488step0 raw488step0Labels = mixedMoment B raw488step1 raw488step1Labels := by
      have ha : raw488step1 = raw488step0 := by apply Matrix.ext; unfold raw488step1 raw488step0; decide +kernel
      have hl : raw488step0Labels = labelEmbedding1 ∘ raw488step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw488step0 raw488step0Labels raw488step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3734 node3734Labels := by rfl

def raw489 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw489Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw489step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw489 raw489Labels = mixedMoment B node445 node445Labels := by
  calc
    mixedMoment B raw489 raw489Labels = mixedMoment B raw489step0 raw489step0Labels := by
      have ha : raw489step0 = (fun i j => raw489 (permutation283 i) (permutation4 j)) := by apply Matrix.ext; unfold raw489step0 raw489; decide +kernel
      have hl : raw489step0Labels = raw489Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw489 raw489Labels permutation283 permutation4
    _ = mixedMoment B node445 node445Labels := by rfl

def raw490 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw490Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw490 raw490Labels = mixedMoment B node3735 node3735Labels := by
  calc
    mixedMoment B raw490 raw490Labels = mixedMoment B raw490step0 raw490step0Labels := by
      have ha : raw490step0 = (fun i j => raw490 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw490step0 raw490; decide +kernel
      have hl : raw490step0Labels = raw490Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw490 raw490Labels permutation152 permutation5
    mixedMoment B raw490step0 raw490step0Labels = mixedMoment B raw490step1 raw490step1Labels := by
      have ha : raw490step1 = raw490step0 := by apply Matrix.ext; unfold raw490step1 raw490step0; decide +kernel
      have hl : raw490step0Labels = labelEmbedding1 ∘ raw490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw490step0 raw490step0Labels raw490step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3735 node3735Labels := by rfl

def raw491 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw491Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw491step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw491 raw491Labels = mixedMoment B node448 node448Labels := by
  calc
    mixedMoment B raw491 raw491Labels = mixedMoment B raw491step0 raw491step0Labels := by
      have ha : raw491step0 = (fun i j => raw491 (permutation281 i) (permutation4 j)) := by apply Matrix.ext; unfold raw491step0 raw491; decide +kernel
      have hl : raw491step0Labels = raw491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw491 raw491Labels permutation281 permutation4
    _ = mixedMoment B node448 node448Labels := by rfl

def raw492 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw492 raw492Labels = mixedMoment B node3736 node3736Labels := by
  calc
    mixedMoment B raw492 raw492Labels = mixedMoment B raw492step0 raw492step0Labels := by
      have ha : raw492step0 = (fun i j => raw492 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw492step0 raw492; decide +kernel
      have hl : raw492step0Labels = raw492Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw492 raw492Labels permutation32 permutation5
    mixedMoment B raw492step0 raw492step0Labels = mixedMoment B raw492step1 raw492step1Labels := by
      have ha : raw492step1 = raw492step0 := by apply Matrix.ext; unfold raw492step1 raw492step0; decide +kernel
      have hl : raw492step0Labels = labelEmbedding1 ∘ raw492step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw492step0 raw492step0Labels raw492step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3736 node3736Labels := by rfl

def raw493 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw493Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw493step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw493 raw493Labels = mixedMoment B node449 node449Labels := by
  calc
    mixedMoment B raw493 raw493Labels = mixedMoment B raw493step0 raw493step0Labels := by
      have ha : raw493step0 = (fun i j => raw493 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw493step0 raw493; decide +kernel
      have hl : raw493step0Labels = raw493Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw493 raw493Labels permutation32 permutation5
    _ = mixedMoment B node449 node449Labels := by rfl

def raw494 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw494step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw494 raw494Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw494 raw494Labels = mixedMoment B raw494step0 raw494step0Labels := by
      have ha : raw494step0 = (fun i j => raw494 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw494step0 raw494; decide +kernel
      have hl : raw494step0Labels = raw494Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw494 raw494Labels permutation32 permutation5
    mixedMoment B raw494step0 raw494step0Labels = mixedMoment B raw494step1 raw494step1Labels := by
      have ha : raw494step1 = raw494step0 := by apply Matrix.ext; unfold raw494step1 raw494step0; decide +kernel
      have hl : raw494step0Labels = labelEmbedding1 ∘ raw494step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw494step0 raw494step0Labels raw494step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw495 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw495Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw495step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw495 raw495Labels = mixedMoment B node450 node450Labels := by
  calc
    mixedMoment B raw495 raw495Labels = mixedMoment B raw495step0 raw495step0Labels := by
      have ha : raw495step0 = (fun i j => raw495 (permutation58 i) (permutation4 j)) := by apply Matrix.ext; unfold raw495step0 raw495; decide +kernel
      have hl : raw495step0Labels = raw495Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw495 raw495Labels permutation58 permutation4
    _ = mixedMoment B node450 node450Labels := by rfl

def raw496 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw496 raw496Labels = mixedMoment B node3738 node3738Labels := by
  calc
    mixedMoment B raw496 raw496Labels = mixedMoment B raw496step0 raw496step0Labels := by
      have ha : raw496step0 = (fun i j => raw496 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw496step0 raw496; decide +kernel
      have hl : raw496step0Labels = raw496Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw496 raw496Labels permutation32 permutation5
    mixedMoment B raw496step0 raw496step0Labels = mixedMoment B raw496step1 raw496step1Labels := by
      have ha : raw496step1 = raw496step0 := by apply Matrix.ext; unfold raw496step1 raw496step0; decide +kernel
      have hl : raw496step0Labels = labelEmbedding1 ∘ raw496step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw496step0 raw496step0Labels raw496step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3738 node3738Labels := by rfl

def raw497 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw497Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw497step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw497 raw497Labels = mixedMoment B node446 node446Labels := by
  calc
    mixedMoment B raw497 raw497Labels = mixedMoment B raw497step0 raw497step0Labels := by
      have ha : raw497step0 = (fun i j => raw497 (permutation58 i) (permutation4 j)) := by apply Matrix.ext; unfold raw497step0 raw497; decide +kernel
      have hl : raw497step0Labels = raw497Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw497 raw497Labels permutation58 permutation4
    _ = mixedMoment B node446 node446Labels := by rfl

def raw498 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw498 raw498Labels = mixedMoment B node3739 node3739Labels := by
  calc
    mixedMoment B raw498 raw498Labels = mixedMoment B raw498step0 raw498step0Labels := by
      have ha : raw498step0 = (fun i j => raw498 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw498step0 raw498; decide +kernel
      have hl : raw498step0Labels = raw498Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw498 raw498Labels permutation32 permutation5
    mixedMoment B raw498step0 raw498step0Labels = mixedMoment B raw498step1 raw498step1Labels := by
      have ha : raw498step1 = raw498step0 := by apply Matrix.ext; unfold raw498step1 raw498step0; decide +kernel
      have hl : raw498step0Labels = labelEmbedding1 ∘ raw498step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw498step0 raw498step0Labels raw498step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3739 node3739Labels := by rfl

def raw499 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw499Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw499step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw499 raw499Labels = mixedMoment B node449 node449Labels := by
  calc
    mixedMoment B raw499 raw499Labels = mixedMoment B raw499step0 raw499step0Labels := by
      have ha : raw499step0 = (fun i j => raw499 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw499step0 raw499; decide +kernel
      have hl : raw499step0Labels = raw499Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw499 raw499Labels permutation56 permutation4
    _ = mixedMoment B node449 node449Labels := by rfl

def raw500 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 2, -2], ![-2, 2, 0]]
def raw500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw500step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw500step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw500 raw500Labels = mixedMoment B node3740 node3740Labels := by
  calc
    mixedMoment B raw500 raw500Labels = mixedMoment B raw500step0 raw500step0Labels := by
      have ha : raw500step0 = (fun i j => raw500 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw500step0 raw500; decide +kernel
      have hl : raw500step0Labels = raw500Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw500 raw500Labels permutation8 permutation5
    mixedMoment B raw500step0 raw500step0Labels = mixedMoment B raw500step1 raw500step1Labels := by
      have ha : raw500step1 = raw500step0 := by apply Matrix.ext; unfold raw500step1 raw500step0; decide +kernel
      have hl : raw500step0Labels = labelEmbedding1 ∘ raw500step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw500step0 raw500step0Labels raw500step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3740 node3740Labels := by rfl

def raw501 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 2, -2], ![-2, 2, 0]]
def raw501Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw501step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw501step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw501 raw501Labels = mixedMoment B node451 node451Labels := by
  calc
    mixedMoment B raw501 raw501Labels = mixedMoment B raw501step0 raw501step0Labels := by
      have ha : raw501step0 = (fun i j => raw501 (permutation15 i) (permutation4 j)) := by apply Matrix.ext; unfold raw501step0 raw501; decide +kernel
      have hl : raw501step0Labels = raw501Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw501 raw501Labels permutation15 permutation4
    _ = mixedMoment B node451 node451Labels := by rfl

def raw502 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw502step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw502 raw502Labels = mixedMoment B node3741 node3741Labels := by
  calc
    mixedMoment B raw502 raw502Labels = mixedMoment B raw502step0 raw502step0Labels := by
      have ha : raw502step0 = (fun i j => raw502 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw502step0 raw502; decide +kernel
      have hl : raw502step0Labels = raw502Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw502 raw502Labels permutation8 permutation5
    mixedMoment B raw502step0 raw502step0Labels = mixedMoment B raw502step1 raw502step1Labels := by
      have ha : raw502step1 = raw502step0 := by apply Matrix.ext; unfold raw502step1 raw502step0; decide +kernel
      have hl : raw502step0Labels = labelEmbedding1 ∘ raw502step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw502step0 raw502step0Labels raw502step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3741 node3741Labels := by rfl

def raw503 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw503Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw503step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw503step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw503 raw503Labels = mixedMoment B node452 node452Labels := by
  calc
    mixedMoment B raw503 raw503Labels = mixedMoment B raw503step0 raw503step0Labels := by
      have ha : raw503step0 = (fun i j => raw503 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw503step0 raw503; decide +kernel
      have hl : raw503step0Labels = raw503Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw503 raw503Labels permutation14 permutation4
    _ = mixedMoment B node452 node452Labels := by rfl

def raw504 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw504 raw504Labels = mixedMoment B node3818 node3818Labels := by
  calc
    mixedMoment B raw504 raw504Labels = mixedMoment B raw504step0 raw504step0Labels := by
      have ha : raw504step0 = (fun i j => raw504 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw504step0 raw504; decide +kernel
      have hl : raw504step0Labels = raw504Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw504 raw504Labels permutation152 permutation5
    mixedMoment B raw504step0 raw504step0Labels = mixedMoment B raw504step1 raw504step1Labels := by
      have ha : raw504step1 = raw504step0 := by apply Matrix.ext; unfold raw504step1 raw504step0; decide +kernel
      have hl : raw504step0Labels = labelEmbedding1 ∘ raw504step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw504step0 raw504step0Labels raw504step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3818 node3818Labels := by rfl

def raw505 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw505Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw505step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw505step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw505 raw505Labels = mixedMoment B node431 node431Labels := by
  calc
    mixedMoment B raw505 raw505Labels = mixedMoment B raw505step0 raw505step0Labels := by
      have ha : raw505step0 = (fun i j => raw505 (permutation587 i) (permutation4 j)) := by apply Matrix.ext; unfold raw505step0 raw505; decide +kernel
      have hl : raw505step0Labels = raw505Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw505 raw505Labels permutation587 permutation4
    mixedMoment B raw505step0 raw505step0Labels = mixedMoment B raw505step1 raw505step1Labels := by
      have ha : raw505step1 = -raw505step0 := by apply Matrix.ext; change ∀ i j, raw505step1 i j = -(raw505step0 i j); unfold raw505step1 raw505step0; decide +kernel
      have hl : raw505step1Labels = raw505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node431 node431Labels := by rfl

def raw506 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw506step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw506 raw506Labels = mixedMoment B node3820 node3820Labels := by
  calc
    mixedMoment B raw506 raw506Labels = mixedMoment B raw506step0 raw506step0Labels := by
      have ha : raw506step0 = (fun i j => raw506 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw506step0 raw506; decide +kernel
      have hl : raw506step0Labels = raw506Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw506 raw506Labels permutation152 permutation5
    mixedMoment B raw506step0 raw506step0Labels = mixedMoment B raw506step1 raw506step1Labels := by
      have ha : raw506step1 = raw506step0 := by apply Matrix.ext; unfold raw506step1 raw506step0; decide +kernel
      have hl : raw506step0Labels = labelEmbedding1 ∘ raw506step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw506step0 raw506step0Labels raw506step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3820 node3820Labels := by rfl

def raw507 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw507Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw507step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw507 raw507Labels = mixedMoment B node471 node471Labels := by
  calc
    mixedMoment B raw507 raw507Labels = mixedMoment B raw507step0 raw507step0Labels := by
      have ha : raw507step0 = (fun i j => raw507 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw507step0 raw507; decide +kernel
      have hl : raw507step0Labels = raw507Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw507 raw507Labels permutation152 permutation5
    _ = mixedMoment B node471 node471Labels := by rfl

def raw508 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw508 raw508Labels = mixedMoment B node3821 node3821Labels := by
  calc
    mixedMoment B raw508 raw508Labels = mixedMoment B raw508step0 raw508step0Labels := by
      have ha : raw508step0 = (fun i j => raw508 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw508step0 raw508; decide +kernel
      have hl : raw508step0Labels = raw508Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw508 raw508Labels permutation152 permutation5
    mixedMoment B raw508step0 raw508step0Labels = mixedMoment B raw508step1 raw508step1Labels := by
      have ha : raw508step1 = raw508step0 := by apply Matrix.ext; unfold raw508step1 raw508step0; decide +kernel
      have hl : raw508step0Labels = labelEmbedding1 ∘ raw508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw508step0 raw508step0Labels raw508step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3821 node3821Labels := by rfl

def raw509 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw509Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw509step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw509 raw509Labels = mixedMoment B node472 node472Labels := by
  calc
    mixedMoment B raw509 raw509Labels = mixedMoment B raw509step0 raw509step0Labels := by
      have ha : raw509step0 = (fun i j => raw509 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw509step0 raw509; decide +kernel
      have hl : raw509step0Labels = raw509Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw509 raw509Labels permutation152 permutation5
    _ = mixedMoment B node472 node472Labels := by rfl

def raw510 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw510 raw510Labels = mixedMoment B node3822 node3822Labels := by
  calc
    mixedMoment B raw510 raw510Labels = mixedMoment B raw510step0 raw510step0Labels := by
      have ha : raw510step0 = (fun i j => raw510 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw510step0 raw510; decide +kernel
      have hl : raw510step0Labels = raw510Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw510 raw510Labels permutation152 permutation5
    mixedMoment B raw510step0 raw510step0Labels = mixedMoment B raw510step1 raw510step1Labels := by
      have ha : raw510step1 = raw510step0 := by apply Matrix.ext; unfold raw510step1 raw510step0; decide +kernel
      have hl : raw510step0Labels = labelEmbedding1 ∘ raw510step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw510step0 raw510step0Labels raw510step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3822 node3822Labels := by rfl

def raw511 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw511Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw511step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw511step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw511 raw511Labels = mixedMoment B node459 node459Labels := by
  calc
    mixedMoment B raw511 raw511Labels = mixedMoment B raw511step0 raw511step0Labels := by
      have ha : raw511step0 = (fun i j => raw511 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw511step0 raw511; decide +kernel
      have hl : raw511step0Labels = raw511Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw511 raw511Labels permutation662 permutation4
    mixedMoment B raw511step0 raw511step0Labels = mixedMoment B raw511step1 raw511step1Labels := by
      have ha : raw511step1 = -raw511step0 := by apply Matrix.ext; change ∀ i j, raw511step1 i j = -(raw511step0 i j); unfold raw511step1 raw511step0; decide +kernel
      have hl : raw511step1Labels = raw511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node459 node459Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
