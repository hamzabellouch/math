import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw128 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw128step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw128 raw128Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw128 raw128Labels = mixedMoment B raw128step0 raw128step0Labels := by
      have ha : raw128step0 = (fun i j => raw128 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw128step0 raw128; decide +kernel
      have hl : raw128step0Labels = raw128Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw128 raw128Labels permutation32 permutation5
    mixedMoment B raw128step0 raw128step0Labels = mixedMoment B raw128step1 raw128step1Labels := by
      have ha : raw128step1 = raw128step0 := by apply Matrix.ext; unfold raw128step1 raw128step0; decide +kernel
      have hl : raw128step0Labels = labelEmbedding1 ∘ raw128step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw128step0 raw128step0Labels raw128step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw129 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw129Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw129step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw129 raw129Labels = mixedMoment B node93 node93Labels := by
  calc
    mixedMoment B raw129 raw129Labels = mixedMoment B raw129step0 raw129step0Labels := by
      have ha : raw129step0 = (fun i j => raw129 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw129step0 raw129; decide +kernel
      have hl : raw129step0Labels = raw129Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw129 raw129Labels permutation34 permutation4
    _ = mixedMoment B node93 node93Labels := by rfl

def raw130 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw130step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw130 raw130Labels = mixedMoment B node1412 node1412Labels := by
  calc
    mixedMoment B raw130 raw130Labels = mixedMoment B raw130step0 raw130step0Labels := by
      have ha : raw130step0 = (fun i j => raw130 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw130step0 raw130; decide +kernel
      have hl : raw130step0Labels = raw130Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw130 raw130Labels permutation32 permutation5
    mixedMoment B raw130step0 raw130step0Labels = mixedMoment B raw130step1 raw130step1Labels := by
      have ha : raw130step1 = raw130step0 := by apply Matrix.ext; unfold raw130step1 raw130step0; decide +kernel
      have hl : raw130step0Labels = labelEmbedding1 ∘ raw130step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw130step0 raw130step0Labels raw130step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1412 node1412Labels := by rfl

def raw131 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw131Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw131step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw131 raw131Labels = mixedMoment B node89 node89Labels := by
  calc
    mixedMoment B raw131 raw131Labels = mixedMoment B raw131step0 raw131step0Labels := by
      have ha : raw131step0 = (fun i j => raw131 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw131step0 raw131; decide +kernel
      have hl : raw131step0Labels = raw131Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw131 raw131Labels permutation34 permutation4
    _ = mixedMoment B node89 node89Labels := by rfl

def raw132 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw132step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw132step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw132 raw132Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw132 raw132Labels = mixedMoment B raw132step0 raw132step0Labels := by
      have ha : raw132step0 = (fun i j => raw132 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw132step0 raw132; decide +kernel
      have hl : raw132step0Labels = raw132Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw132 raw132Labels permutation8 permutation5
    mixedMoment B raw132step0 raw132step0Labels = mixedMoment B raw132step1 raw132step1Labels := by
      have ha : raw132step1 = raw132step0 := by apply Matrix.ext; unfold raw132step1 raw132step0; decide +kernel
      have hl : raw132step0Labels = labelEmbedding1 ∘ raw132step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw132step0 raw132step0Labels raw132step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw133 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw133Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw133step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw133step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw133 raw133Labels = mixedMoment B node96 node96Labels := by
  calc
    mixedMoment B raw133 raw133Labels = mixedMoment B raw133step0 raw133step0Labels := by
      have ha : raw133step0 = (fun i j => raw133 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw133step0 raw133; decide +kernel
      have hl : raw133step0Labels = raw133Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw133 raw133Labels permutation8 permutation4
    _ = mixedMoment B node96 node96Labels := by rfl

def raw134 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw134step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw134 raw134Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw134 raw134Labels = mixedMoment B raw134step0 raw134step0Labels := by
      have ha : raw134step0 = (fun i j => raw134 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw134step0 raw134; decide +kernel
      have hl : raw134step0Labels = raw134Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw134 raw134Labels permutation32 permutation5
    mixedMoment B raw134step0 raw134step0Labels = mixedMoment B raw134step1 raw134step1Labels := by
      have ha : raw134step1 = raw134step0 := by apply Matrix.ext; unfold raw134step1 raw134step0; decide +kernel
      have hl : raw134step0Labels = labelEmbedding1 ∘ raw134step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw134step0 raw134step0Labels raw134step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1414 node1414Labels := by rfl

def raw135 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw135Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw135step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw135 raw135Labels = mixedMoment B node92 node92Labels := by
  calc
    mixedMoment B raw135 raw135Labels = mixedMoment B raw135step0 raw135step0Labels := by
      have ha : raw135step0 = (fun i j => raw135 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw135step0 raw135; decide +kernel
      have hl : raw135step0Labels = raw135Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw135 raw135Labels permutation32 permutation4
    _ = mixedMoment B node92 node92Labels := by rfl

def raw136 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw136step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw136step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw136 raw136Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw136 raw136Labels = mixedMoment B raw136step0 raw136step0Labels := by
      have ha : raw136step0 = (fun i j => raw136 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw136step0 raw136; decide +kernel
      have hl : raw136step0Labels = raw136Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw136 raw136Labels permutation8 permutation5
    mixedMoment B raw136step0 raw136step0Labels = mixedMoment B raw136step1 raw136step1Labels := by
      have ha : raw136step1 = raw136step0 := by apply Matrix.ext; unfold raw136step1 raw136step0; decide +kernel
      have hl : raw136step0Labels = labelEmbedding1 ∘ raw136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw136step0 raw136step0Labels raw136step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw137 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw137Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw137step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw137step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw137 raw137Labels = mixedMoment B node94 node94Labels := by
  calc
    mixedMoment B raw137 raw137Labels = mixedMoment B raw137step0 raw137step0Labels := by
      have ha : raw137step0 = (fun i j => raw137 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw137step0 raw137; decide +kernel
      have hl : raw137step0Labels = raw137Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw137 raw137Labels permutation8 permutation4
    _ = mixedMoment B node94 node94Labels := by rfl

def raw138 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw138step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw138step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw138 raw138Labels = mixedMoment B node1417 node1417Labels := by
  calc
    mixedMoment B raw138 raw138Labels = mixedMoment B raw138step0 raw138step0Labels := by
      have ha : raw138step0 = (fun i j => raw138 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw138step0 raw138; decide +kernel
      have hl : raw138step0Labels = raw138Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw138 raw138Labels permutation8 permutation5
    mixedMoment B raw138step0 raw138step0Labels = mixedMoment B raw138step1 raw138step1Labels := by
      have ha : raw138step1 = raw138step0 := by apply Matrix.ext; unfold raw138step1 raw138step0; decide +kernel
      have hl : raw138step0Labels = labelEmbedding1 ∘ raw138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw138step0 raw138step0Labels raw138step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1417 node1417Labels := by rfl

def raw139 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw139Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw139step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw139step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw139 raw139Labels = mixedMoment B node90 node90Labels := by
  calc
    mixedMoment B raw139 raw139Labels = mixedMoment B raw139step0 raw139step0Labels := by
      have ha : raw139step0 = (fun i j => raw139 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw139step0 raw139; decide +kernel
      have hl : raw139step0Labels = raw139Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw139 raw139Labels permutation8 permutation4
    _ = mixedMoment B node90 node90Labels := by rfl

def raw140 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw140step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw140step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw140 raw140Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw140 raw140Labels = mixedMoment B raw140step0 raw140step0Labels := by
      have ha : raw140step0 = (fun i j => raw140 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw140step0 raw140; decide +kernel
      have hl : raw140step0Labels = raw140Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw140 raw140Labels permutation8 permutation5
    mixedMoment B raw140step0 raw140step0Labels = mixedMoment B raw140step1 raw140step1Labels := by
      have ha : raw140step1 = raw140step0 := by apply Matrix.ext; unfold raw140step1 raw140step0; decide +kernel
      have hl : raw140step0Labels = labelEmbedding1 ∘ raw140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw140step0 raw140step0Labels raw140step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw141 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw141Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw141step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw141step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw141 raw141Labels = mixedMoment B node98 node98Labels := by
  calc
    mixedMoment B raw141 raw141Labels = mixedMoment B raw141step0 raw141step0Labels := by
      have ha : raw141step0 = (fun i j => raw141 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw141step0 raw141; decide +kernel
      have hl : raw141step0Labels = raw141Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw141 raw141Labels permutation9 permutation4
    _ = mixedMoment B node98 node98Labels := by rfl

def raw142 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw142step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw142step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw142step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw142 raw142Labels = mixedMoment B node1420 node1420Labels := by
  calc
    mixedMoment B raw142 raw142Labels = mixedMoment B raw142step0 raw142step0Labels := by
      have ha : raw142step0 = (fun i j => raw142 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw142step0 raw142; decide +kernel
      have hl : raw142step0Labels = raw142Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw142 raw142Labels permutation8 permutation5
    mixedMoment B raw142step0 raw142step0Labels = mixedMoment B raw142step1 raw142step1Labels := by
      have ha : raw142step1 = raw142step0 := by apply Matrix.ext; unfold raw142step1 raw142step0; decide +kernel
      have hl : raw142step0Labels = labelEmbedding1 ∘ raw142step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw142step0 raw142step0Labels raw142step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1420 node1420Labels := by rfl

def raw143 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw143Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw143step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw143step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw143 raw143Labels = mixedMoment B node99 node99Labels := by
  calc
    mixedMoment B raw143 raw143Labels = mixedMoment B raw143step0 raw143step0Labels := by
      have ha : raw143step0 = (fun i j => raw143 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw143step0 raw143; decide +kernel
      have hl : raw143step0Labels = raw143Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw143 raw143Labels permutation8 permutation4
    _ = mixedMoment B node99 node99Labels := by rfl

def raw144 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 1, -2], ![-1, 1, 0], ![0, 2, -2]]
def raw144Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw144step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw144step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw144 raw144Labels = mixedMoment B node1426 node1426Labels := by
  calc
    mixedMoment B raw144 raw144Labels = mixedMoment B raw144step0 raw144step0Labels := by
      have ha : raw144step0 = (fun i j => raw144 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw144step0 raw144; decide +kernel
      have hl : raw144step0Labels = raw144Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw144 raw144Labels permutation32 permutation5
    mixedMoment B raw144step0 raw144step0Labels = mixedMoment B raw144step1 raw144step1Labels := by
      have ha : raw144step1 = raw144step0 := by apply Matrix.ext; unfold raw144step1 raw144step0; decide +kernel
      have hl : raw144step0Labels = labelEmbedding1 ∘ raw144step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw144step0 raw144step0Labels raw144step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1426 node1426Labels := by rfl

def raw145 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 1, -2], ![-1, 1, 0], ![0, 2, -2]]
def raw145Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw145step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw145 raw145Labels = mixedMoment B node84 node84Labels := by
  calc
    mixedMoment B raw145 raw145Labels = mixedMoment B raw145step0 raw145step0Labels := by
      have ha : raw145step0 = (fun i j => raw145 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw145step0 raw145; decide +kernel
      have hl : raw145step0Labels = raw145Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw145 raw145Labels permutation34 permutation4
    _ = mixedMoment B node84 node84Labels := by rfl

def raw146 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 2, -3]]
def raw146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw146step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw146step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw146 raw146Labels = mixedMoment B node1427 node1427Labels := by
  calc
    mixedMoment B raw146 raw146Labels = mixedMoment B raw146step0 raw146step0Labels := by
      have ha : raw146step0 = (fun i j => raw146 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw146step0 raw146; decide +kernel
      have hl : raw146step0Labels = raw146Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw146 raw146Labels permutation32 permutation5
    mixedMoment B raw146step0 raw146step0Labels = mixedMoment B raw146step1 raw146step1Labels := by
      have ha : raw146step1 = raw146step0 := by apply Matrix.ext; unfold raw146step1 raw146step0; decide +kernel
      have hl : raw146step0Labels = labelEmbedding1 ∘ raw146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw146step0 raw146step0Labels raw146step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1427 node1427Labels := by rfl

def raw147 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 2, -3]]
def raw147Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw147step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw147 raw147Labels = mixedMoment B node83 node83Labels := by
  calc
    mixedMoment B raw147 raw147Labels = mixedMoment B raw147step0 raw147step0Labels := by
      have ha : raw147step0 = (fun i j => raw147 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw147step0 raw147; decide +kernel
      have hl : raw147step0Labels = raw147Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw147 raw147Labels permutation34 permutation4
    _ = mixedMoment B node83 node83Labels := by rfl

def raw148 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 3, -4]]
def raw148Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw148step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw148step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw148step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw148 raw148Labels = mixedMoment B node1429 node1429Labels := by
  calc
    mixedMoment B raw148 raw148Labels = mixedMoment B raw148step0 raw148step0Labels := by
      have ha : raw148step0 = (fun i j => raw148 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw148step0 raw148; decide +kernel
      have hl : raw148step0Labels = raw148Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw148 raw148Labels permutation8 permutation5
    mixedMoment B raw148step0 raw148step0Labels = mixedMoment B raw148step1 raw148step1Labels := by
      have ha : raw148step1 = raw148step0 := by apply Matrix.ext; unfold raw148step1 raw148step0; decide +kernel
      have hl : raw148step0Labels = labelEmbedding1 ∘ raw148step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw148step0 raw148step0Labels raw148step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1429 node1429Labels := by rfl

def raw149 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 3, -4]]
def raw149Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw149step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw149step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw149 raw149Labels = mixedMoment B node85 node85Labels := by
  calc
    mixedMoment B raw149 raw149Labels = mixedMoment B raw149step0 raw149step0Labels := by
      have ha : raw149step0 = (fun i j => raw149 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw149step0 raw149; decide +kernel
      have hl : raw149step0Labels = raw149Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw149 raw149Labels permutation8 permutation4
    _ = mixedMoment B node85 node85Labels := by rfl

def raw150 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 2, -3], ![-1, 2, -1]]
def raw150Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw150step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw150step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw150step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw150 raw150Labels = mixedMoment B node1430 node1430Labels := by
  calc
    mixedMoment B raw150 raw150Labels = mixedMoment B raw150step0 raw150step0Labels := by
      have ha : raw150step0 = (fun i j => raw150 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw150step0 raw150; decide +kernel
      have hl : raw150step0Labels = raw150Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw150 raw150Labels permutation8 permutation5
    mixedMoment B raw150step0 raw150step0Labels = mixedMoment B raw150step1 raw150step1Labels := by
      have ha : raw150step1 = raw150step0 := by apply Matrix.ext; unfold raw150step1 raw150step0; decide +kernel
      have hl : raw150step0Labels = labelEmbedding1 ∘ raw150step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw150step0 raw150step0Labels raw150step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1430 node1430Labels := by rfl

def raw151 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 2, -3], ![-1, 2, -1]]
def raw151Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw151step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw151step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw151 raw151Labels = mixedMoment B node86 node86Labels := by
  calc
    mixedMoment B raw151 raw151Labels = mixedMoment B raw151step0 raw151step0Labels := by
      have ha : raw151step0 = (fun i j => raw151 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw151step0 raw151; decide +kernel
      have hl : raw151step0Labels = raw151Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw151 raw151Labels permutation9 permutation4
    _ = mixedMoment B node86 node86Labels := by rfl

def raw152 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw152Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw152step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw152 raw152Labels = mixedMoment B node1441 node1441Labels := by
  calc
    mixedMoment B raw152 raw152Labels = mixedMoment B raw152step0 raw152step0Labels := by
      have ha : raw152step0 = (fun i j => raw152 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw152step0 raw152; decide +kernel
      have hl : raw152step0Labels = raw152Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw152 raw152Labels permutation32 permutation5
    mixedMoment B raw152step0 raw152step0Labels = mixedMoment B raw152step1 raw152step1Labels := by
      have ha : raw152step1 = raw152step0 := by apply Matrix.ext; unfold raw152step1 raw152step0; decide +kernel
      have hl : raw152step0Labels = labelEmbedding1 ∘ raw152step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw152step0 raw152step0Labels raw152step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1441 node1441Labels := by rfl

def raw153 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw153Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw153step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw153 raw153Labels = mixedMoment B node108 node108Labels := by
  calc
    mixedMoment B raw153 raw153Labels = mixedMoment B raw153step0 raw153step0Labels := by
      have ha : raw153step0 = (fun i j => raw153 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw153step0 raw153; decide +kernel
      have hl : raw153step0Labels = raw153Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw153 raw153Labels permutation49 permutation4
    _ = mixedMoment B node108 node108Labels := by rfl

def raw154 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw154Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw154step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw154step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw154 raw154Labels = mixedMoment B node1442 node1442Labels := by
  calc
    mixedMoment B raw154 raw154Labels = mixedMoment B raw154step0 raw154step0Labels := by
      have ha : raw154step0 = (fun i j => raw154 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw154step0 raw154; decide +kernel
      have hl : raw154step0Labels = raw154Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw154 raw154Labels permutation8 permutation5
    mixedMoment B raw154step0 raw154step0Labels = mixedMoment B raw154step1 raw154step1Labels := by
      have ha : raw154step1 = raw154step0 := by apply Matrix.ext; unfold raw154step1 raw154step0; decide +kernel
      have hl : raw154step0Labels = labelEmbedding1 ∘ raw154step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw154step0 raw154step0Labels raw154step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1442 node1442Labels := by rfl

def raw155 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw155Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw155step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw155step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw155 raw155Labels = mixedMoment B node111 node111Labels := by
  calc
    mixedMoment B raw155 raw155Labels = mixedMoment B raw155step0 raw155step0Labels := by
      have ha : raw155step0 = (fun i j => raw155 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw155step0 raw155; decide +kernel
      have hl : raw155step0Labels = raw155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw155 raw155Labels permutation10 permutation4
    _ = mixedMoment B node111 node111Labels := by rfl

def raw156 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw156step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw156step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw156 raw156Labels = mixedMoment B node1443 node1443Labels := by
  calc
    mixedMoment B raw156 raw156Labels = mixedMoment B raw156step0 raw156step0Labels := by
      have ha : raw156step0 = (fun i j => raw156 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw156step0 raw156; decide +kernel
      have hl : raw156step0Labels = raw156Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw156 raw156Labels permutation8 permutation5
    mixedMoment B raw156step0 raw156step0Labels = mixedMoment B raw156step1 raw156step1Labels := by
      have ha : raw156step1 = raw156step0 := by apply Matrix.ext; unfold raw156step1 raw156step0; decide +kernel
      have hl : raw156step0Labels = labelEmbedding1 ∘ raw156step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw156step0 raw156step0Labels raw156step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1443 node1443Labels := by rfl

def raw157 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw157Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw157step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw157step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw157 raw157Labels = mixedMoment B node110 node110Labels := by
  calc
    mixedMoment B raw157 raw157Labels = mixedMoment B raw157step0 raw157step0Labels := by
      have ha : raw157step0 = (fun i j => raw157 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw157step0 raw157; decide +kernel
      have hl : raw157step0Labels = raw157Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw157 raw157Labels permutation10 permutation4
    _ = mixedMoment B node110 node110Labels := by rfl

def raw158 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 1, 1], ![0, 2, -2]]
def raw158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw158step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw158step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw158 raw158Labels = mixedMoment B node1444 node1444Labels := by
  calc
    mixedMoment B raw158 raw158Labels = mixedMoment B raw158step0 raw158step0Labels := by
      have ha : raw158step0 = (fun i j => raw158 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw158step0 raw158; decide +kernel
      have hl : raw158step0Labels = raw158Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw158 raw158Labels permutation8 permutation5
    mixedMoment B raw158step0 raw158step0Labels = mixedMoment B raw158step1 raw158step1Labels := by
      have ha : raw158step1 = raw158step0 := by apply Matrix.ext; unfold raw158step1 raw158step0; decide +kernel
      have hl : raw158step0Labels = labelEmbedding1 ∘ raw158step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw158step0 raw158step0Labels raw158step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1444 node1444Labels := by rfl

def raw159 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 1, 1], ![0, 2, -2]]
def raw159Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw159step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw159step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw159 raw159Labels = mixedMoment B node106 node106Labels := by
  calc
    mixedMoment B raw159 raw159Labels = mixedMoment B raw159step0 raw159step0Labels := by
      have ha : raw159step0 = (fun i j => raw159 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw159step0 raw159; decide +kernel
      have hl : raw159step0Labels = raw159Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw159 raw159Labels permutation10 permutation4
    _ = mixedMoment B node106 node106Labels := by rfl

def raw160 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 3, -1]]
def raw160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw160step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw160step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw160step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw160 raw160Labels = mixedMoment B node1445 node1445Labels := by
  calc
    mixedMoment B raw160 raw160Labels = mixedMoment B raw160step0 raw160step0Labels := by
      have ha : raw160step0 = (fun i j => raw160 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw160step0 raw160; decide +kernel
      have hl : raw160step0Labels = raw160Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw160 raw160Labels permutation2 permutation5
    mixedMoment B raw160step0 raw160step0Labels = mixedMoment B raw160step1 raw160step1Labels := by
      have ha : raw160step1 = raw160step0 := by apply Matrix.ext; unfold raw160step1 raw160step0; decide +kernel
      have hl : raw160step0Labels = labelEmbedding1 ∘ raw160step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw160step0 raw160step0Labels raw160step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1445 node1445Labels := by rfl

def raw161 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 3, -1]]
def raw161Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw161step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw161step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw161 raw161Labels = mixedMoment B node112 node112Labels := by
  calc
    mixedMoment B raw161 raw161Labels = mixedMoment B raw161step0 raw161step0Labels := by
      have ha : raw161step0 = (fun i j => raw161 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw161step0 raw161; decide +kernel
      have hl : raw161step0Labels = raw161Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw161 raw161Labels permutation2 permutation4
    _ = mixedMoment B node112 node112Labels := by rfl

def raw162 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 1, -1], ![-2, 1, 1], ![1, 2, -3]]
def raw162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw162step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw162step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw162 raw162Labels = mixedMoment B node1449 node1449Labels := by
  calc
    mixedMoment B raw162 raw162Labels = mixedMoment B raw162step0 raw162step0Labels := by
      have ha : raw162step0 = (fun i j => raw162 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw162step0 raw162; decide +kernel
      have hl : raw162step0Labels = raw162Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw162 raw162Labels permutation8 permutation5
    mixedMoment B raw162step0 raw162step0Labels = mixedMoment B raw162step1 raw162step1Labels := by
      have ha : raw162step1 = raw162step0 := by apply Matrix.ext; unfold raw162step1 raw162step0; decide +kernel
      have hl : raw162step0Labels = labelEmbedding1 ∘ raw162step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw162step0 raw162step0Labels raw162step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1449 node1449Labels := by rfl

def raw163 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 1, -1], ![-2, 1, 1], ![1, 2, -3]]
def raw163Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw163step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw163step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw163 raw163Labels = mixedMoment B node105 node105Labels := by
  calc
    mixedMoment B raw163 raw163Labels = mixedMoment B raw163step0 raw163step0Labels := by
      have ha : raw163step0 = (fun i j => raw163 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw163step0 raw163; decide +kernel
      have hl : raw163step0Labels = raw163Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw163 raw163Labels permutation10 permutation4
    _ = mixedMoment B node105 node105Labels := by rfl

def raw164 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw164step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw164 raw164Labels = mixedMoment B node1451 node1451Labels := by
  calc
    mixedMoment B raw164 raw164Labels = mixedMoment B raw164step0 raw164step0Labels := by
      have ha : raw164step0 = (fun i j => raw164 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw164step0 raw164; decide +kernel
      have hl : raw164step0Labels = raw164Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw164 raw164Labels permutation8 permutation5
    mixedMoment B raw164step0 raw164step0Labels = mixedMoment B raw164step1 raw164step1Labels := by
      have ha : raw164step1 = raw164step0 := by apply Matrix.ext; unfold raw164step1 raw164step0; decide +kernel
      have hl : raw164step0Labels = labelEmbedding1 ∘ raw164step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw164step0 raw164step0Labels raw164step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1451 node1451Labels := by rfl

def raw165 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw165Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw165step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw165step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw165 raw165Labels = mixedMoment B node109 node109Labels := by
  calc
    mixedMoment B raw165 raw165Labels = mixedMoment B raw165step0 raw165step0Labels := by
      have ha : raw165step0 = (fun i j => raw165 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw165step0 raw165; decide +kernel
      have hl : raw165step0Labels = raw165Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw165 raw165Labels permutation8 permutation4
    _ = mixedMoment B node109 node109Labels := by rfl

def raw166 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw166step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw166step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw166 raw166Labels = mixedMoment B node1453 node1453Labels := by
  calc
    mixedMoment B raw166 raw166Labels = mixedMoment B raw166step0 raw166step0Labels := by
      have ha : raw166step0 = (fun i j => raw166 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw166step0 raw166; decide +kernel
      have hl : raw166step0Labels = raw166Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw166 raw166Labels permutation2 permutation5
    mixedMoment B raw166step0 raw166step0Labels = mixedMoment B raw166step1 raw166step1Labels := by
      have ha : raw166step1 = raw166step0 := by apply Matrix.ext; unfold raw166step1 raw166step0; decide +kernel
      have hl : raw166step0Labels = labelEmbedding1 ∘ raw166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw166step0 raw166step0Labels raw166step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1453 node1453Labels := by rfl

def raw167 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw167Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw167step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw167step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw167 raw167Labels = mixedMoment B node107 node107Labels := by
  calc
    mixedMoment B raw167 raw167Labels = mixedMoment B raw167step0 raw167step0Labels := by
      have ha : raw167step0 = (fun i j => raw167 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw167step0 raw167; decide +kernel
      have hl : raw167step0Labels = raw167Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw167 raw167Labels permutation2 permutation4
    _ = mixedMoment B node107 node107Labels := by rfl

def raw168 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 2, -3], ![-2, 2, 0]]
def raw168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw168step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw168step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw168 raw168Labels = mixedMoment B node1454 node1454Labels := by
  calc
    mixedMoment B raw168 raw168Labels = mixedMoment B raw168step0 raw168step0Labels := by
      have ha : raw168step0 = (fun i j => raw168 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw168step0 raw168; decide +kernel
      have hl : raw168step0Labels = raw168Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw168 raw168Labels permutation2 permutation5
    mixedMoment B raw168step0 raw168step0Labels = mixedMoment B raw168step1 raw168step1Labels := by
      have ha : raw168step1 = raw168step0 := by apply Matrix.ext; unfold raw168step1 raw168step0; decide +kernel
      have hl : raw168step0Labels = labelEmbedding1 ∘ raw168step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw168step0 raw168step0Labels raw168step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1454 node1454Labels := by rfl

def raw169 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 2, -3], ![-2, 2, 0]]
def raw169Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw169step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw169step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw169 raw169Labels = mixedMoment B node113 node113Labels := by
  calc
    mixedMoment B raw169 raw169Labels = mixedMoment B raw169step0 raw169step0Labels := by
      have ha : raw169step0 = (fun i j => raw169 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw169step0 raw169; decide +kernel
      have hl : raw169step0Labels = raw169Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw169 raw169Labels permutation3 permutation4
    _ = mixedMoment B node113 node113Labels := by rfl

def raw170 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw170step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw170 raw170Labels = mixedMoment B node1468 node1468Labels := by
  calc
    mixedMoment B raw170 raw170Labels = mixedMoment B raw170step0 raw170step0Labels := by
      have ha : raw170step0 = (fun i j => raw170 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw170step0 raw170; decide +kernel
      have hl : raw170step0Labels = raw170Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw170 raw170Labels permutation32 permutation5
    mixedMoment B raw170step0 raw170step0Labels = mixedMoment B raw170step1 raw170step1Labels := by
      have ha : raw170step1 = raw170step0 := by apply Matrix.ext; unfold raw170step1 raw170step0; decide +kernel
      have hl : raw170step0Labels = labelEmbedding1 ∘ raw170step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw170step0 raw170step0Labels raw170step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1468 node1468Labels := by rfl

def raw171 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw171Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw171step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw171step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw171 raw171Labels = mixedMoment B node51 node51Labels := by
  calc
    mixedMoment B raw171 raw171Labels = mixedMoment B raw171step0 raw171step0Labels := by
      have ha : raw171step0 = (fun i j => raw171 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw171step0 raw171; decide +kernel
      have hl : raw171step0Labels = raw171Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw171 raw171Labels permutation47 permutation6
    mixedMoment B raw171step0 raw171step0Labels = mixedMoment B raw171step1 raw171step1Labels := by
      have ha : raw171step1 = -raw171step0 := by apply Matrix.ext; change ∀ i j, raw171step1 i j = -(raw171step0 i j); unfold raw171step1 raw171step0; decide +kernel
      have hl : raw171step1Labels = raw171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node51 node51Labels := by rfl

def raw172 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw172step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw172step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw172 raw172Labels = mixedMoment B node1469 node1469Labels := by
  calc
    mixedMoment B raw172 raw172Labels = mixedMoment B raw172step0 raw172step0Labels := by
      have ha : raw172step0 = (fun i j => raw172 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw172step0 raw172; decide +kernel
      have hl : raw172step0Labels = raw172Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw172 raw172Labels permutation8 permutation5
    mixedMoment B raw172step0 raw172step0Labels = mixedMoment B raw172step1 raw172step1Labels := by
      have ha : raw172step1 = raw172step0 := by apply Matrix.ext; unfold raw172step1 raw172step0; decide +kernel
      have hl : raw172step0Labels = labelEmbedding1 ∘ raw172step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw172step0 raw172step0Labels raw172step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1469 node1469Labels := by rfl

def raw173 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw173Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw173step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw173step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw173 raw173Labels = mixedMoment B node54 node54Labels := by
  calc
    mixedMoment B raw173 raw173Labels = mixedMoment B raw173step0 raw173step0Labels := by
      have ha : raw173step0 = (fun i j => raw173 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw173step0 raw173; decide +kernel
      have hl : raw173step0Labels = raw173Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw173 raw173Labels permutation8 permutation4
    _ = mixedMoment B node54 node54Labels := by rfl

def raw174 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw174 raw174Labels = mixedMoment B node1470 node1470Labels := by
  calc
    mixedMoment B raw174 raw174Labels = mixedMoment B raw174step0 raw174step0Labels := by
      have ha : raw174step0 = (fun i j => raw174 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw174step0 raw174; decide +kernel
      have hl : raw174step0Labels = raw174Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw174 raw174Labels permutation32 permutation5
    mixedMoment B raw174step0 raw174step0Labels = mixedMoment B raw174step1 raw174step1Labels := by
      have ha : raw174step1 = raw174step0 := by apply Matrix.ext; unfold raw174step1 raw174step0; decide +kernel
      have hl : raw174step0Labels = labelEmbedding1 ∘ raw174step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw174step0 raw174step0Labels raw174step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1470 node1470Labels := by rfl

def raw175 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw175Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw175step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw175step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw175 raw175Labels = mixedMoment B node47 node47Labels := by
  calc
    mixedMoment B raw175 raw175Labels = mixedMoment B raw175step0 raw175step0Labels := by
      have ha : raw175step0 = (fun i j => raw175 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw175step0 raw175; decide +kernel
      have hl : raw175step0Labels = raw175Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw175 raw175Labels permutation40 permutation6
    mixedMoment B raw175step0 raw175step0Labels = mixedMoment B raw175step1 raw175step1Labels := by
      have ha : raw175step1 = -raw175step0 := by apply Matrix.ext; change ∀ i j, raw175step1 i j = -(raw175step0 i j); unfold raw175step1 raw175step0; decide +kernel
      have hl : raw175step1Labels = raw175step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node47 node47Labels := by rfl

def raw176 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 3, -2]]
def raw176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw176step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw176 raw176Labels = mixedMoment B node1471 node1471Labels := by
  calc
    mixedMoment B raw176 raw176Labels = mixedMoment B raw176step0 raw176step0Labels := by
      have ha : raw176step0 = (fun i j => raw176 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw176step0 raw176; decide +kernel
      have hl : raw176step0Labels = raw176Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw176 raw176Labels permutation8 permutation5
    mixedMoment B raw176step0 raw176step0Labels = mixedMoment B raw176step1 raw176step1Labels := by
      have ha : raw176step1 = raw176step0 := by apply Matrix.ext; unfold raw176step1 raw176step0; decide +kernel
      have hl : raw176step0Labels = labelEmbedding1 ∘ raw176step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw176step0 raw176step0Labels raw176step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1471 node1471Labels := by rfl

def raw177 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 3, -2]]
def raw177Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw177step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw177step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw177step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw177 raw177Labels = mixedMoment B node53 node53Labels := by
  calc
    mixedMoment B raw177 raw177Labels = mixedMoment B raw177step0 raw177step0Labels := by
      have ha : raw177step0 = (fun i j => raw177 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw177step0 raw177; decide +kernel
      have hl : raw177step0Labels = raw177Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw177 raw177Labels permutation10 permutation6
    mixedMoment B raw177step0 raw177step0Labels = mixedMoment B raw177step1 raw177step1Labels := by
      have ha : raw177step1 = -raw177step0 := by apply Matrix.ext; change ∀ i j, raw177step1 i j = -(raw177step0 i j); unfold raw177step1 raw177step0; decide +kernel
      have hl : raw177step1Labels = raw177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node53 node53Labels := by rfl

def raw178 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 2, -2], ![-2, 2, 0]]
def raw178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw178step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw178 raw178Labels = mixedMoment B node1472 node1472Labels := by
  calc
    mixedMoment B raw178 raw178Labels = mixedMoment B raw178step0 raw178step0Labels := by
      have ha : raw178step0 = (fun i j => raw178 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw178step0 raw178; decide +kernel
      have hl : raw178step0Labels = raw178Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw178 raw178Labels permutation8 permutation5
    mixedMoment B raw178step0 raw178step0Labels = mixedMoment B raw178step1 raw178step1Labels := by
      have ha : raw178step1 = raw178step0 := by apply Matrix.ext; unfold raw178step1 raw178step0; decide +kernel
      have hl : raw178step0Labels = labelEmbedding1 ∘ raw178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw178step0 raw178step0Labels raw178step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1472 node1472Labels := by rfl

def raw179 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 2, -2], ![-2, 2, 0]]
def raw179Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw179step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw179step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw179 raw179Labels = mixedMoment B node55 node55Labels := by
  calc
    mixedMoment B raw179 raw179Labels = mixedMoment B raw179step0 raw179step0Labels := by
      have ha : raw179step0 = (fun i j => raw179 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw179step0 raw179; decide +kernel
      have hl : raw179step0Labels = raw179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw179 raw179Labels permutation9 permutation4
    _ = mixedMoment B node55 node55Labels := by rfl

def raw180 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw180step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw180 raw180Labels = mixedMoment B node1473 node1473Labels := by
  calc
    mixedMoment B raw180 raw180Labels = mixedMoment B raw180step0 raw180step0Labels := by
      have ha : raw180step0 = (fun i j => raw180 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw180step0 raw180; decide +kernel
      have hl : raw180step0Labels = raw180Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw180 raw180Labels permutation8 permutation5
    mixedMoment B raw180step0 raw180step0Labels = mixedMoment B raw180step1 raw180step1Labels := by
      have ha : raw180step1 = raw180step0 := by apply Matrix.ext; unfold raw180step1 raw180step0; decide +kernel
      have hl : raw180step0Labels = labelEmbedding1 ∘ raw180step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw180step0 raw180step0Labels raw180step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1473 node1473Labels := by rfl

def raw181 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw181Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw181step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw181 raw181Labels = mixedMoment B node56 node56Labels := by
  calc
    mixedMoment B raw181 raw181Labels = mixedMoment B raw181step0 raw181step0Labels := by
      have ha : raw181step0 = (fun i j => raw181 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw181step0 raw181; decide +kernel
      have hl : raw181step0Labels = raw181Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw181 raw181Labels permutation8 permutation4
    _ = mixedMoment B node56 node56Labels := by rfl

def raw182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw182 raw182Labels = mixedMoment B node1475 node1475Labels := by
  calc
    mixedMoment B raw182 raw182Labels = mixedMoment B raw182step0 raw182step0Labels := by
      have ha : raw182step0 = (fun i j => raw182 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw182step0 raw182; decide +kernel
      have hl : raw182step0Labels = raw182Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw182 raw182Labels permutation152 permutation5
    mixedMoment B raw182step0 raw182step0Labels = mixedMoment B raw182step1 raw182step1Labels := by
      have ha : raw182step1 = raw182step0 := by apply Matrix.ext; unfold raw182step1 raw182step0; decide +kernel
      have hl : raw182step0Labels = labelEmbedding1 ∘ raw182step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw182step0 raw182step0Labels raw182step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1475 node1475Labels := by rfl

def raw183 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw183Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw183step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw183 raw183Labels = mixedMoment B node44 node44Labels := by
  calc
    mixedMoment B raw183 raw183Labels = mixedMoment B raw183step0 raw183step0Labels := by
      have ha : raw183step0 = (fun i j => raw183 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw183step0 raw183; decide +kernel
      have hl : raw183step0Labels = raw183Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw183 raw183Labels permutation154 permutation4
    _ = mixedMoment B node44 node44Labels := by rfl

def raw184 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw184 raw184Labels = mixedMoment B node1476 node1476Labels := by
  calc
    mixedMoment B raw184 raw184Labels = mixedMoment B raw184step0 raw184step0Labels := by
      have ha : raw184step0 = (fun i j => raw184 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw184step0 raw184; decide +kernel
      have hl : raw184step0Labels = raw184Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw184 raw184Labels permutation32 permutation5
    mixedMoment B raw184step0 raw184step0Labels = mixedMoment B raw184step1 raw184step1Labels := by
      have ha : raw184step1 = raw184step0 := by apply Matrix.ext; unfold raw184step1 raw184step0; decide +kernel
      have hl : raw184step0Labels = labelEmbedding1 ∘ raw184step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw184step0 raw184step0Labels raw184step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1476 node1476Labels := by rfl

def raw185 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw185Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw185step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw185 raw185Labels = mixedMoment B node46 node46Labels := by
  calc
    mixedMoment B raw185 raw185Labels = mixedMoment B raw185step0 raw185step0Labels := by
      have ha : raw185step0 = (fun i j => raw185 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw185step0 raw185; decide +kernel
      have hl : raw185step0Labels = raw185Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw185 raw185Labels permutation32 permutation4
    _ = mixedMoment B node46 node46Labels := by rfl

def raw186 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw186 raw186Labels = mixedMoment B node1477 node1477Labels := by
  calc
    mixedMoment B raw186 raw186Labels = mixedMoment B raw186step0 raw186step0Labels := by
      have ha : raw186step0 = (fun i j => raw186 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw186step0 raw186; decide +kernel
      have hl : raw186step0Labels = raw186Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw186 raw186Labels permutation152 permutation5
    mixedMoment B raw186step0 raw186step0Labels = mixedMoment B raw186step1 raw186step1Labels := by
      have ha : raw186step1 = raw186step0 := by apply Matrix.ext; unfold raw186step1 raw186step0; decide +kernel
      have hl : raw186step0Labels = labelEmbedding1 ∘ raw186step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw186step0 raw186step0Labels raw186step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1477 node1477Labels := by rfl

def raw187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw187Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw187step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw187 raw187Labels = mixedMoment B node43 node43Labels := by
  calc
    mixedMoment B raw187 raw187Labels = mixedMoment B raw187step0 raw187step0Labels := by
      have ha : raw187step0 = (fun i j => raw187 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw187step0 raw187; decide +kernel
      have hl : raw187step0Labels = raw187Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw187 raw187Labels permutation152 permutation4
    _ = mixedMoment B node43 node43Labels := by rfl

def raw188 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw188 raw188Labels = mixedMoment B node1478 node1478Labels := by
  calc
    mixedMoment B raw188 raw188Labels = mixedMoment B raw188step0 raw188step0Labels := by
      have ha : raw188step0 = (fun i j => raw188 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw188step0 raw188; decide +kernel
      have hl : raw188step0Labels = raw188Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw188 raw188Labels permutation32 permutation5
    mixedMoment B raw188step0 raw188step0Labels = mixedMoment B raw188step1 raw188step1Labels := by
      have ha : raw188step1 = raw188step0 := by apply Matrix.ext; unfold raw188step1 raw188step0; decide +kernel
      have hl : raw188step0Labels = labelEmbedding1 ∘ raw188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw188step0 raw188step0Labels raw188step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1478 node1478Labels := by rfl

def raw189 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw189Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw189step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw189 raw189Labels = mixedMoment B node45 node45Labels := by
  calc
    mixedMoment B raw189 raw189Labels = mixedMoment B raw189step0 raw189step0Labels := by
      have ha : raw189step0 = (fun i j => raw189 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw189step0 raw189; decide +kernel
      have hl : raw189step0Labels = raw189Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw189 raw189Labels permutation32 permutation4
    _ = mixedMoment B node45 node45Labels := by rfl

def raw190 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw190 raw190Labels = mixedMoment B node1479 node1479Labels := by
  calc
    mixedMoment B raw190 raw190Labels = mixedMoment B raw190step0 raw190step0Labels := by
      have ha : raw190step0 = (fun i j => raw190 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw190step0 raw190; decide +kernel
      have hl : raw190step0Labels = raw190Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw190 raw190Labels permutation32 permutation5
    mixedMoment B raw190step0 raw190step0Labels = mixedMoment B raw190step1 raw190step1Labels := by
      have ha : raw190step1 = raw190step0 := by apply Matrix.ext; unfold raw190step1 raw190step0; decide +kernel
      have hl : raw190step0Labels = labelEmbedding1 ∘ raw190step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw190step0 raw190step0Labels raw190step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1479 node1479Labels := by rfl

def raw191 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw191Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw191step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw191 raw191Labels = mixedMoment B node48 node48Labels := by
  calc
    mixedMoment B raw191 raw191Labels = mixedMoment B raw191step0 raw191step0Labels := by
      have ha : raw191step0 = (fun i j => raw191 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw191step0 raw191; decide +kernel
      have hl : raw191step0Labels = raw191Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw191 raw191Labels permutation32 permutation4
    _ = mixedMoment B node48 node48Labels := by rfl

def raw192 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw192 raw192Labels = mixedMoment B node1480 node1480Labels := by
  calc
    mixedMoment B raw192 raw192Labels = mixedMoment B raw192step0 raw192step0Labels := by
      have ha : raw192step0 = (fun i j => raw192 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw192step0 raw192; decide +kernel
      have hl : raw192step0Labels = raw192Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw192 raw192Labels permutation32 permutation5
    mixedMoment B raw192step0 raw192step0Labels = mixedMoment B raw192step1 raw192step1Labels := by
      have ha : raw192step1 = raw192step0 := by apply Matrix.ext; unfold raw192step1 raw192step0; decide +kernel
      have hl : raw192step0Labels = labelEmbedding1 ∘ raw192step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw192step0 raw192step0Labels raw192step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1480 node1480Labels := by rfl

def raw193 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw193Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw193step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw193 raw193Labels = mixedMoment B node50 node50Labels := by
  calc
    mixedMoment B raw193 raw193Labels = mixedMoment B raw193step0 raw193step0Labels := by
      have ha : raw193step0 = (fun i j => raw193 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw193step0 raw193; decide +kernel
      have hl : raw193step0Labels = raw193Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw193 raw193Labels permutation34 permutation4
    _ = mixedMoment B node50 node50Labels := by rfl

def raw194 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw194step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw194 raw194Labels = mixedMoment B node1481 node1481Labels := by
  calc
    mixedMoment B raw194 raw194Labels = mixedMoment B raw194step0 raw194step0Labels := by
      have ha : raw194step0 = (fun i j => raw194 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw194step0 raw194; decide +kernel
      have hl : raw194step0Labels = raw194Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw194 raw194Labels permutation8 permutation5
    mixedMoment B raw194step0 raw194step0Labels = mixedMoment B raw194step1 raw194step1Labels := by
      have ha : raw194step1 = raw194step0 := by apply Matrix.ext; unfold raw194step1 raw194step0; decide +kernel
      have hl : raw194step0Labels = labelEmbedding1 ∘ raw194step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw194step0 raw194step0Labels raw194step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1481 node1481Labels := by rfl

def raw195 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw195Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw195step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw195step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw195 raw195Labels = mixedMoment B node52 node52Labels := by
  calc
    mixedMoment B raw195 raw195Labels = mixedMoment B raw195step0 raw195step0Labels := by
      have ha : raw195step0 = (fun i j => raw195 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw195step0 raw195; decide +kernel
      have hl : raw195step0Labels = raw195Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw195 raw195Labels permutation8 permutation4
    _ = mixedMoment B node52 node52Labels := by rfl

def raw196 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw196 raw196Labels = mixedMoment B node2357 node2357Labels := by
  calc
    mixedMoment B raw196 raw196Labels = mixedMoment B raw196step0 raw196step0Labels := by
      have ha : raw196step0 = (fun i j => raw196 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw196step0 raw196; decide +kernel
      have hl : raw196step0Labels = raw196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw196 raw196Labels permutation32 permutation5
    mixedMoment B raw196step0 raw196step0Labels = mixedMoment B raw196step1 raw196step1Labels := by
      have ha : raw196step1 = raw196step0 := by apply Matrix.ext; unfold raw196step1 raw196step0; decide +kernel
      have hl : raw196step0Labels = labelEmbedding1 ∘ raw196step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw196step0 raw196step0Labels raw196step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2357 node2357Labels := by rfl

def raw197 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw197Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw197step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw197 raw197Labels = mixedMoment B node284 node284Labels := by
  calc
    mixedMoment B raw197 raw197Labels = mixedMoment B raw197step0 raw197step0Labels := by
      have ha : raw197step0 = (fun i j => raw197 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw197step0 raw197; decide +kernel
      have hl : raw197step0Labels = raw197Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw197 raw197Labels permutation32 permutation5
    _ = mixedMoment B node284 node284Labels := by rfl

def raw198 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw198 raw198Labels = mixedMoment B node2358 node2358Labels := by
  calc
    mixedMoment B raw198 raw198Labels = mixedMoment B raw198step0 raw198step0Labels := by
      have ha : raw198step0 = (fun i j => raw198 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw198step0 raw198; decide +kernel
      have hl : raw198step0Labels = raw198Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw198 raw198Labels permutation32 permutation5
    mixedMoment B raw198step0 raw198step0Labels = mixedMoment B raw198step1 raw198step1Labels := by
      have ha : raw198step1 = raw198step0 := by apply Matrix.ext; unfold raw198step1 raw198step0; decide +kernel
      have hl : raw198step0Labels = labelEmbedding1 ∘ raw198step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw198step0 raw198step0Labels raw198step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2358 node2358Labels := by rfl

def raw199 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw199Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw199step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw199 raw199Labels = mixedMoment B node285 node285Labels := by
  calc
    mixedMoment B raw199 raw199Labels = mixedMoment B raw199step0 raw199step0Labels := by
      have ha : raw199step0 = (fun i j => raw199 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw199step0 raw199; decide +kernel
      have hl : raw199step0Labels = raw199Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw199 raw199Labels permutation32 permutation5
    _ = mixedMoment B node285 node285Labels := by rfl

def raw200 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw200step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw200 raw200Labels = mixedMoment B node2359 node2359Labels := by
  calc
    mixedMoment B raw200 raw200Labels = mixedMoment B raw200step0 raw200step0Labels := by
      have ha : raw200step0 = (fun i j => raw200 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw200step0 raw200; decide +kernel
      have hl : raw200step0Labels = raw200Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw200 raw200Labels permutation32 permutation5
    mixedMoment B raw200step0 raw200step0Labels = mixedMoment B raw200step1 raw200step1Labels := by
      have ha : raw200step1 = raw200step0 := by apply Matrix.ext; unfold raw200step1 raw200step0; decide +kernel
      have hl : raw200step0Labels = labelEmbedding1 ∘ raw200step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw200step0 raw200step0Labels raw200step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2359 node2359Labels := by rfl

def raw201 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw201Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw201step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw201 raw201Labels = mixedMoment B node286 node286Labels := by
  calc
    mixedMoment B raw201 raw201Labels = mixedMoment B raw201step0 raw201step0Labels := by
      have ha : raw201step0 = (fun i j => raw201 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw201step0 raw201; decide +kernel
      have hl : raw201step0Labels = raw201Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw201 raw201Labels permutation32 permutation5
    _ = mixedMoment B node286 node286Labels := by rfl

def raw202 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw202step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw202 raw202Labels = mixedMoment B node2360 node2360Labels := by
  calc
    mixedMoment B raw202 raw202Labels = mixedMoment B raw202step0 raw202step0Labels := by
      have ha : raw202step0 = (fun i j => raw202 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw202step0 raw202; decide +kernel
      have hl : raw202step0Labels = raw202Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw202 raw202Labels permutation32 permutation5
    mixedMoment B raw202step0 raw202step0Labels = mixedMoment B raw202step1 raw202step1Labels := by
      have ha : raw202step1 = raw202step0 := by apply Matrix.ext; unfold raw202step1 raw202step0; decide +kernel
      have hl : raw202step0Labels = labelEmbedding1 ∘ raw202step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw202step0 raw202step0Labels raw202step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2360 node2360Labels := by rfl

def raw203 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw203Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw203step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw203 raw203Labels = mixedMoment B node287 node287Labels := by
  calc
    mixedMoment B raw203 raw203Labels = mixedMoment B raw203step0 raw203step0Labels := by
      have ha : raw203step0 = (fun i j => raw203 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw203step0 raw203; decide +kernel
      have hl : raw203step0Labels = raw203Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw203 raw203Labels permutation32 permutation5
    _ = mixedMoment B node287 node287Labels := by rfl

def raw204 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-2, 2, 0], ![0, 3, -3]]
def raw204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw204step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw204 raw204Labels = mixedMoment B node2363 node2363Labels := by
  calc
    mixedMoment B raw204 raw204Labels = mixedMoment B raw204step0 raw204step0Labels := by
      have ha : raw204step0 = (fun i j => raw204 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw204step0 raw204; decide +kernel
      have hl : raw204step0Labels = raw204Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw204 raw204Labels permutation8 permutation5
    mixedMoment B raw204step0 raw204step0Labels = mixedMoment B raw204step1 raw204step1Labels := by
      have ha : raw204step1 = raw204step0 := by apply Matrix.ext; unfold raw204step1 raw204step0; decide +kernel
      have hl : raw204step0Labels = labelEmbedding1 ∘ raw204step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw204step0 raw204step0Labels raw204step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2363 node2363Labels := by rfl

def raw205 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-2, 2, 0], ![0, 3, -3]]
def raw205Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw205step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw205step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw205 raw205Labels = mixedMoment B node187 node187Labels := by
  calc
    mixedMoment B raw205 raw205Labels = mixedMoment B raw205step0 raw205step0Labels := by
      have ha : raw205step0 = (fun i j => raw205 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw205step0 raw205; decide +kernel
      have hl : raw205step0Labels = raw205Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw205 raw205Labels permutation31 permutation4
    mixedMoment B raw205step0 raw205step0Labels = mixedMoment B raw205step1 raw205step1Labels := by
      have ha : raw205step1 = -raw205step0 := by apply Matrix.ext; change ∀ i j, raw205step1 i j = -(raw205step0 i j); unfold raw205step1 raw205step0; decide +kernel
      have hl : raw205step1Labels = raw205step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node187 node187Labels := by rfl

def raw206 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw206step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw206 raw206Labels = mixedMoment B node2526 node2526Labels := by
  calc
    mixedMoment B raw206 raw206Labels = mixedMoment B raw206step0 raw206step0Labels := by
      have ha : raw206step0 = (fun i j => raw206 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw206step0 raw206; decide +kernel
      have hl : raw206step0Labels = raw206Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw206 raw206Labels permutation152 permutation5
    mixedMoment B raw206step0 raw206step0Labels = mixedMoment B raw206step1 raw206step1Labels := by
      have ha : raw206step1 = raw206step0 := by apply Matrix.ext; unfold raw206step1 raw206step0; decide +kernel
      have hl : raw206step0Labels = labelEmbedding1 ∘ raw206step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw206step0 raw206step0Labels raw206step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2526 node2526Labels := by rfl

def raw207 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw207Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw207step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw207step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw207 raw207Labels = mixedMoment B node294 node294Labels := by
  calc
    mixedMoment B raw207 raw207Labels = mixedMoment B raw207step0 raw207step0Labels := by
      have ha : raw207step0 = (fun i j => raw207 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw207step0 raw207; decide +kernel
      have hl : raw207step0Labels = raw207Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw207 raw207Labels permutation662 permutation4
    mixedMoment B raw207step0 raw207step0Labels = mixedMoment B raw207step1 raw207step1Labels := by
      have ha : raw207step1 = -raw207step0 := by apply Matrix.ext; change ∀ i j, raw207step1 i j = -(raw207step0 i j); unfold raw207step1 raw207step0; decide +kernel
      have hl : raw207step1Labels = raw207step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node294 node294Labels := by rfl

def raw208 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw208 raw208Labels = mixedMoment B node2527 node2527Labels := by
  calc
    mixedMoment B raw208 raw208Labels = mixedMoment B raw208step0 raw208step0Labels := by
      have ha : raw208step0 = (fun i j => raw208 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw208step0 raw208; decide +kernel
      have hl : raw208step0Labels = raw208Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw208 raw208Labels permutation152 permutation5
    mixedMoment B raw208step0 raw208step0Labels = mixedMoment B raw208step1 raw208step1Labels := by
      have ha : raw208step1 = raw208step0 := by apply Matrix.ext; unfold raw208step1 raw208step0; decide +kernel
      have hl : raw208step0Labels = labelEmbedding1 ∘ raw208step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw208step0 raw208step0Labels raw208step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2527 node2527Labels := by rfl

def raw209 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw209Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw209step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw209 raw209Labels = mixedMoment B node317 node317Labels := by
  calc
    mixedMoment B raw209 raw209Labels = mixedMoment B raw209step0 raw209step0Labels := by
      have ha : raw209step0 = (fun i j => raw209 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw209step0 raw209; decide +kernel
      have hl : raw209step0Labels = raw209Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw209 raw209Labels permutation152 permutation5
    _ = mixedMoment B node317 node317Labels := by rfl

def raw210 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw210 raw210Labels = mixedMoment B node2528 node2528Labels := by
  calc
    mixedMoment B raw210 raw210Labels = mixedMoment B raw210step0 raw210step0Labels := by
      have ha : raw210step0 = (fun i j => raw210 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw210step0 raw210; decide +kernel
      have hl : raw210step0Labels = raw210Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw210 raw210Labels permutation152 permutation5
    mixedMoment B raw210step0 raw210step0Labels = mixedMoment B raw210step1 raw210step1Labels := by
      have ha : raw210step1 = raw210step0 := by apply Matrix.ext; unfold raw210step1 raw210step0; decide +kernel
      have hl : raw210step0Labels = labelEmbedding1 ∘ raw210step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw210step0 raw210step0Labels raw210step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2528 node2528Labels := by rfl

def raw211 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw211Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw211step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw211step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw211 raw211Labels = mixedMoment B node207 node207Labels := by
  calc
    mixedMoment B raw211 raw211Labels = mixedMoment B raw211step0 raw211step0Labels := by
      have ha : raw211step0 = (fun i j => raw211 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw211step0 raw211; decide +kernel
      have hl : raw211step0Labels = raw211Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw211 raw211Labels permutation662 permutation4
    mixedMoment B raw211step0 raw211step0Labels = mixedMoment B raw211step1 raw211step1Labels := by
      have ha : raw211step1 = -raw211step0 := by apply Matrix.ext; change ∀ i j, raw211step1 i j = -(raw211step0 i j); unfold raw211step1 raw211step0; decide +kernel
      have hl : raw211step1Labels = raw211step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node207 node207Labels := by rfl

def raw212 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw212 raw212Labels = mixedMoment B node2530 node2530Labels := by
  calc
    mixedMoment B raw212 raw212Labels = mixedMoment B raw212step0 raw212step0Labels := by
      have ha : raw212step0 = (fun i j => raw212 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw212step0 raw212; decide +kernel
      have hl : raw212step0Labels = raw212Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw212 raw212Labels permutation152 permutation5
    mixedMoment B raw212step0 raw212step0Labels = mixedMoment B raw212step1 raw212step1Labels := by
      have ha : raw212step1 = raw212step0 := by apply Matrix.ext; unfold raw212step1 raw212step0; decide +kernel
      have hl : raw212step0Labels = labelEmbedding1 ∘ raw212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw212step0 raw212step0Labels raw212step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2530 node2530Labels := by rfl

def raw213 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw213Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw213step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw213 raw213Labels = mixedMoment B node318 node318Labels := by
  calc
    mixedMoment B raw213 raw213Labels = mixedMoment B raw213step0 raw213step0Labels := by
      have ha : raw213step0 = (fun i j => raw213 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw213step0 raw213; decide +kernel
      have hl : raw213step0Labels = raw213Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw213 raw213Labels permutation152 permutation5
    _ = mixedMoment B node318 node318Labels := by rfl

def raw214 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw214 raw214Labels = mixedMoment B node2531 node2531Labels := by
  calc
    mixedMoment B raw214 raw214Labels = mixedMoment B raw214step0 raw214step0Labels := by
      have ha : raw214step0 = (fun i j => raw214 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw214step0 raw214; decide +kernel
      have hl : raw214step0Labels = raw214Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw214 raw214Labels permutation32 permutation5
    mixedMoment B raw214step0 raw214step0Labels = mixedMoment B raw214step1 raw214step1Labels := by
      have ha : raw214step1 = raw214step0 := by apply Matrix.ext; unfold raw214step1 raw214step0; decide +kernel
      have hl : raw214step0Labels = labelEmbedding1 ∘ raw214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw214step0 raw214step0Labels raw214step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2531 node2531Labels := by rfl

def raw215 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw215Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw215step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw215step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw215 raw215Labels = mixedMoment B node274 node274Labels := by
  calc
    mixedMoment B raw215 raw215Labels = mixedMoment B raw215step0 raw215step0Labels := by
      have ha : raw215step0 = (fun i j => raw215 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw215step0 raw215; decide +kernel
      have hl : raw215step0Labels = raw215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw215 raw215Labels permutation149 permutation4
    mixedMoment B raw215step0 raw215step0Labels = mixedMoment B raw215step1 raw215step1Labels := by
      have ha : raw215step1 = -raw215step0 := by apply Matrix.ext; change ∀ i j, raw215step1 i j = -(raw215step0 i j); unfold raw215step1 raw215step0; decide +kernel
      have hl : raw215step1Labels = raw215step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node274 node274Labels := by rfl

def raw216 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw216step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw216 raw216Labels = mixedMoment B node2532 node2532Labels := by
  calc
    mixedMoment B raw216 raw216Labels = mixedMoment B raw216step0 raw216step0Labels := by
      have ha : raw216step0 = (fun i j => raw216 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw216step0 raw216; decide +kernel
      have hl : raw216step0Labels = raw216Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw216 raw216Labels permutation32 permutation5
    mixedMoment B raw216step0 raw216step0Labels = mixedMoment B raw216step1 raw216step1Labels := by
      have ha : raw216step1 = raw216step0 := by apply Matrix.ext; unfold raw216step1 raw216step0; decide +kernel
      have hl : raw216step0Labels = labelEmbedding1 ∘ raw216step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw216step0 raw216step0Labels raw216step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2532 node2532Labels := by rfl

def raw217 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw217Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw217step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw217step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw217 raw217Labels = mixedMoment B node180 node180Labels := by
  calc
    mixedMoment B raw217 raw217Labels = mixedMoment B raw217step0 raw217step0Labels := by
      have ha : raw217step0 = (fun i j => raw217 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw217step0 raw217; decide +kernel
      have hl : raw217step0Labels = raw217Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw217 raw217Labels permutation149 permutation4
    mixedMoment B raw217step0 raw217step0Labels = mixedMoment B raw217step1 raw217step1Labels := by
      have ha : raw217step1 = -raw217step0 := by apply Matrix.ext; change ∀ i j, raw217step1 i j = -(raw217step0 i j); unfold raw217step1 raw217step0; decide +kernel
      have hl : raw217step1Labels = raw217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node180 node180Labels := by rfl

def raw218 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw218step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw218 raw218Labels = mixedMoment B node2563 node2563Labels := by
  calc
    mixedMoment B raw218 raw218Labels = mixedMoment B raw218step0 raw218step0Labels := by
      have ha : raw218step0 = (fun i j => raw218 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw218step0 raw218; decide +kernel
      have hl : raw218step0Labels = raw218Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw218 raw218Labels permutation152 permutation5
    mixedMoment B raw218step0 raw218step0Labels = mixedMoment B raw218step1 raw218step1Labels := by
      have ha : raw218step1 = raw218step0 := by apply Matrix.ext; unfold raw218step1 raw218step0; decide +kernel
      have hl : raw218step0Labels = labelEmbedding1 ∘ raw218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw218step0 raw218step0Labels raw218step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2563 node2563Labels := by rfl

def raw219 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw219Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw219step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw219step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw219 raw219Labels = mixedMoment B node199 node199Labels := by
  calc
    mixedMoment B raw219 raw219Labels = mixedMoment B raw219step0 raw219step0Labels := by
      have ha : raw219step0 = (fun i j => raw219 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw219step0 raw219; decide +kernel
      have hl : raw219step0Labels = raw219Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw219 raw219Labels permutation682 permutation4
    mixedMoment B raw219step0 raw219step0Labels = mixedMoment B raw219step1 raw219step1Labels := by
      have ha : raw219step1 = -raw219step0 := by apply Matrix.ext; change ∀ i j, raw219step1 i j = -(raw219step0 i j); unfold raw219step1 raw219step0; decide +kernel
      have hl : raw219step1Labels = raw219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node199 node199Labels := by rfl

def raw220 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw220 raw220Labels = mixedMoment B node2570 node2570Labels := by
  calc
    mixedMoment B raw220 raw220Labels = mixedMoment B raw220step0 raw220step0Labels := by
      have ha : raw220step0 = (fun i j => raw220 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw220step0 raw220; decide +kernel
      have hl : raw220step0Labels = raw220Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw220 raw220Labels permutation152 permutation5
    mixedMoment B raw220step0 raw220step0Labels = mixedMoment B raw220step1 raw220step1Labels := by
      have ha : raw220step1 = raw220step0 := by apply Matrix.ext; unfold raw220step1 raw220step0; decide +kernel
      have hl : raw220step0Labels = labelEmbedding1 ∘ raw220step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw220step0 raw220step0Labels raw220step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2570 node2570Labels := by rfl

def raw221 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw221Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw221step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw221 raw221Labels = mixedMoment B node326 node326Labels := by
  calc
    mixedMoment B raw221 raw221Labels = mixedMoment B raw221step0 raw221step0Labels := by
      have ha : raw221step0 = (fun i j => raw221 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw221step0 raw221; decide +kernel
      have hl : raw221step0Labels = raw221Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw221 raw221Labels permutation152 permutation5
    _ = mixedMoment B node326 node326Labels := by rfl

def raw222 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw222 raw222Labels = mixedMoment B node2572 node2572Labels := by
  calc
    mixedMoment B raw222 raw222Labels = mixedMoment B raw222step0 raw222step0Labels := by
      have ha : raw222step0 = (fun i j => raw222 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw222step0 raw222; decide +kernel
      have hl : raw222step0Labels = raw222Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw222 raw222Labels permutation32 permutation5
    mixedMoment B raw222step0 raw222step0Labels = mixedMoment B raw222step1 raw222step1Labels := by
      have ha : raw222step1 = raw222step0 := by apply Matrix.ext; unfold raw222step1 raw222step0; decide +kernel
      have hl : raw222step0Labels = labelEmbedding1 ∘ raw222step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw222step0 raw222step0Labels raw222step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2572 node2572Labels := by rfl

def raw223 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw223Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw223step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw223step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw223 raw223Labels = mixedMoment B node305 node305Labels := by
  calc
    mixedMoment B raw223 raw223Labels = mixedMoment B raw223step0 raw223step0Labels := by
      have ha : raw223step0 = (fun i j => raw223 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw223step0 raw223; decide +kernel
      have hl : raw223step0Labels = raw223Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw223 raw223Labels permutation151 permutation4
    mixedMoment B raw223step0 raw223step0Labels = mixedMoment B raw223step1 raw223step1Labels := by
      have ha : raw223step1 = -raw223step0 := by apply Matrix.ext; change ∀ i j, raw223step1 i j = -(raw223step0 i j); unfold raw223step1 raw223step0; decide +kernel
      have hl : raw223step1Labels = raw223step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node305 node305Labels := by rfl

def raw224 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw224step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw224step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw224 raw224Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw224 raw224Labels = mixedMoment B raw224step0 raw224step0Labels := by
      have ha : raw224step0 = (fun i j => raw224 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw224step0 raw224; decide +kernel
      have hl : raw224step0Labels = raw224Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw224 raw224Labels permutation32 permutation5
    mixedMoment B raw224step0 raw224step0Labels = mixedMoment B raw224step1 raw224step1Labels := by
      have ha : raw224step1 = raw224step0 := by apply Matrix.ext; unfold raw224step1 raw224step0; decide +kernel
      have hl : raw224step0Labels = labelEmbedding1 ∘ raw224step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw224step0 raw224step0Labels raw224step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw225 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw225Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw225step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw225step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw225 raw225Labels = mixedMoment B node224 node224Labels := by
  calc
    mixedMoment B raw225 raw225Labels = mixedMoment B raw225step0 raw225step0Labels := by
      have ha : raw225step0 = (fun i j => raw225 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw225step0 raw225; decide +kernel
      have hl : raw225step0Labels = raw225Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw225 raw225Labels permutation151 permutation4
    mixedMoment B raw225step0 raw225step0Labels = mixedMoment B raw225step1 raw225step1Labels := by
      have ha : raw225step1 = -raw225step0 := by apply Matrix.ext; change ∀ i j, raw225step1 i j = -(raw225step0 i j); unfold raw225step1 raw225step0; decide +kernel
      have hl : raw225step1Labels = raw225step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node224 node224Labels := by rfl

def raw226 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw226Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw226step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw226 raw226Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw226 raw226Labels = mixedMoment B raw226step0 raw226step0Labels := by
      have ha : raw226step0 = (fun i j => raw226 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw226step0 raw226; decide +kernel
      have hl : raw226step0Labels = raw226Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw226 raw226Labels permutation32 permutation5
    mixedMoment B raw226step0 raw226step0Labels = mixedMoment B raw226step1 raw226step1Labels := by
      have ha : raw226step1 = raw226step0 := by apply Matrix.ext; unfold raw226step1 raw226step0; decide +kernel
      have hl : raw226step0Labels = labelEmbedding1 ∘ raw226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw226step0 raw226step0Labels raw226step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw227 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw227Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw227step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw227 raw227Labels = mixedMoment B node329 node329Labels := by
  calc
    mixedMoment B raw227 raw227Labels = mixedMoment B raw227step0 raw227step0Labels := by
      have ha : raw227step0 = (fun i j => raw227 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw227step0 raw227; decide +kernel
      have hl : raw227step0Labels = raw227Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw227 raw227Labels permutation32 permutation5
    _ = mixedMoment B node329 node329Labels := by rfl

def raw228 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw228Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw228step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw228 raw228Labels = mixedMoment B node2581 node2581Labels := by
  calc
    mixedMoment B raw228 raw228Labels = mixedMoment B raw228step0 raw228step0Labels := by
      have ha : raw228step0 = (fun i j => raw228 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw228step0 raw228; decide +kernel
      have hl : raw228step0Labels = raw228Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw228 raw228Labels permutation32 permutation5
    mixedMoment B raw228step0 raw228step0Labels = mixedMoment B raw228step1 raw228step1Labels := by
      have ha : raw228step1 = raw228step0 := by apply Matrix.ext; unfold raw228step1 raw228step0; decide +kernel
      have hl : raw228step0Labels = labelEmbedding1 ∘ raw228step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw228step0 raw228step0Labels raw228step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2581 node2581Labels := by rfl

def raw229 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw229Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw229step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw229step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw229 raw229Labels = mixedMoment B node203 node203Labels := by
  calc
    mixedMoment B raw229 raw229Labels = mixedMoment B raw229step0 raw229step0Labels := by
      have ha : raw229step0 = (fun i j => raw229 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw229step0 raw229; decide +kernel
      have hl : raw229step0Labels = raw229Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw229 raw229Labels permutation151 permutation4
    mixedMoment B raw229step0 raw229step0Labels = mixedMoment B raw229step1 raw229step1Labels := by
      have ha : raw229step1 = -raw229step0 := by apply Matrix.ext; change ∀ i j, raw229step1 i j = -(raw229step0 i j); unfold raw229step1 raw229step0; decide +kernel
      have hl : raw229step1Labels = raw229step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node203 node203Labels := by rfl

def raw230 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw230Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw230step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw230 raw230Labels = mixedMoment B node2593 node2593Labels := by
  calc
    mixedMoment B raw230 raw230Labels = mixedMoment B raw230step0 raw230step0Labels := by
      have ha : raw230step0 = (fun i j => raw230 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw230step0 raw230; decide +kernel
      have hl : raw230step0Labels = raw230Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw230 raw230Labels permutation152 permutation5
    mixedMoment B raw230step0 raw230step0Labels = mixedMoment B raw230step1 raw230step1Labels := by
      have ha : raw230step1 = raw230step0 := by apply Matrix.ext; unfold raw230step1 raw230step0; decide +kernel
      have hl : raw230step0Labels = labelEmbedding1 ∘ raw230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw230step0 raw230step0Labels raw230step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2593 node2593Labels := by rfl

def raw231 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw231Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw231step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw231 raw231Labels = mixedMoment B node334 node334Labels := by
  calc
    mixedMoment B raw231 raw231Labels = mixedMoment B raw231step0 raw231step0Labels := by
      have ha : raw231step0 = (fun i j => raw231 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw231step0 raw231; decide +kernel
      have hl : raw231step0Labels = raw231Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw231 raw231Labels permutation152 permutation5
    _ = mixedMoment B node334 node334Labels := by rfl

def raw232 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw232Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw232step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw232 raw232Labels = mixedMoment B node2594 node2594Labels := by
  calc
    mixedMoment B raw232 raw232Labels = mixedMoment B raw232step0 raw232step0Labels := by
      have ha : raw232step0 = (fun i j => raw232 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw232step0 raw232; decide +kernel
      have hl : raw232step0Labels = raw232Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw232 raw232Labels permutation32 permutation5
    mixedMoment B raw232step0 raw232step0Labels = mixedMoment B raw232step1 raw232step1Labels := by
      have ha : raw232step1 = raw232step0 := by apply Matrix.ext; unfold raw232step1 raw232step0; decide +kernel
      have hl : raw232step0Labels = labelEmbedding1 ∘ raw232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw232step0 raw232step0Labels raw232step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2594 node2594Labels := by rfl

def raw233 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw233Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw233step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw233 raw233Labels = mixedMoment B node335 node335Labels := by
  calc
    mixedMoment B raw233 raw233Labels = mixedMoment B raw233step0 raw233step0Labels := by
      have ha : raw233step0 = (fun i j => raw233 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw233step0 raw233; decide +kernel
      have hl : raw233step0Labels = raw233Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw233 raw233Labels permutation32 permutation5
    _ = mixedMoment B node335 node335Labels := by rfl

def raw234 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw234step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw234 raw234Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw234 raw234Labels = mixedMoment B raw234step0 raw234step0Labels := by
      have ha : raw234step0 = (fun i j => raw234 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw234step0 raw234; decide +kernel
      have hl : raw234step0Labels = raw234Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw234 raw234Labels permutation32 permutation5
    mixedMoment B raw234step0 raw234step0Labels = mixedMoment B raw234step1 raw234step1Labels := by
      have ha : raw234step1 = raw234step0 := by apply Matrix.ext; unfold raw234step1 raw234step0; decide +kernel
      have hl : raw234step0Labels = labelEmbedding1 ∘ raw234step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw234step0 raw234step0Labels raw234step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw235 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw235Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw235step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw235 raw235Labels = mixedMoment B node336 node336Labels := by
  calc
    mixedMoment B raw235 raw235Labels = mixedMoment B raw235step0 raw235step0Labels := by
      have ha : raw235step0 = (fun i j => raw235 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw235step0 raw235; decide +kernel
      have hl : raw235step0Labels = raw235Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw235 raw235Labels permutation32 permutation5
    _ = mixedMoment B node336 node336Labels := by rfl

def raw236 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw236 raw236Labels = mixedMoment B node2596 node2596Labels := by
  calc
    mixedMoment B raw236 raw236Labels = mixedMoment B raw236step0 raw236step0Labels := by
      have ha : raw236step0 = (fun i j => raw236 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw236step0 raw236; decide +kernel
      have hl : raw236step0Labels = raw236Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw236 raw236Labels permutation32 permutation5
    mixedMoment B raw236step0 raw236step0Labels = mixedMoment B raw236step1 raw236step1Labels := by
      have ha : raw236step1 = raw236step0 := by apply Matrix.ext; unfold raw236step1 raw236step0; decide +kernel
      have hl : raw236step0Labels = labelEmbedding1 ∘ raw236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw236step0 raw236step0Labels raw236step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2596 node2596Labels := by rfl

def raw237 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw237Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw237step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw237 raw237Labels = mixedMoment B node337 node337Labels := by
  calc
    mixedMoment B raw237 raw237Labels = mixedMoment B raw237step0 raw237step0Labels := by
      have ha : raw237step0 = (fun i j => raw237 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw237step0 raw237; decide +kernel
      have hl : raw237step0Labels = raw237Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw237 raw237Labels permutation32 permutation5
    _ = mixedMoment B node337 node337Labels := by rfl

def raw238 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 3, -1]]
def raw238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw238step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw238 raw238Labels = mixedMoment B node2598 node2598Labels := by
  calc
    mixedMoment B raw238 raw238Labels = mixedMoment B raw238step0 raw238step0Labels := by
      have ha : raw238step0 = (fun i j => raw238 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw238step0 raw238; decide +kernel
      have hl : raw238step0Labels = raw238Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw238 raw238Labels permutation8 permutation5
    mixedMoment B raw238step0 raw238step0Labels = mixedMoment B raw238step1 raw238step1Labels := by
      have ha : raw238step1 = raw238step0 := by apply Matrix.ext; unfold raw238step1 raw238step0; decide +kernel
      have hl : raw238step0Labels = labelEmbedding1 ∘ raw238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw238step0 raw238step0Labels raw238step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2598 node2598Labels := by rfl

def raw239 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 3, -1]]
def raw239Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw239step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw239step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw239 raw239Labels = mixedMoment B node338 node338Labels := by
  calc
    mixedMoment B raw239 raw239Labels = mixedMoment B raw239step0 raw239step0Labels := by
      have ha : raw239step0 = (fun i j => raw239 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw239step0 raw239; decide +kernel
      have hl : raw239step0Labels = raw239Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw239 raw239Labels permutation8 permutation5
    _ = mixedMoment B node338 node338Labels := by rfl

def raw240 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw240Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw240step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw240 raw240Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw240 raw240Labels = mixedMoment B raw240step0 raw240step0Labels := by
      have ha : raw240step0 = (fun i j => raw240 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw240step0 raw240; decide +kernel
      have hl : raw240step0Labels = raw240Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw240 raw240Labels permutation32 permutation5
    mixedMoment B raw240step0 raw240step0Labels = mixedMoment B raw240step1 raw240step1Labels := by
      have ha : raw240step1 = raw240step0 := by apply Matrix.ext; unfold raw240step1 raw240step0; decide +kernel
      have hl : raw240step0Labels = labelEmbedding1 ∘ raw240step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw240step0 raw240step0Labels raw240step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw241 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw241Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw241step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw241 raw241Labels = mixedMoment B node339 node339Labels := by
  calc
    mixedMoment B raw241 raw241Labels = mixedMoment B raw241step0 raw241step0Labels := by
      have ha : raw241step0 = (fun i j => raw241 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw241step0 raw241; decide +kernel
      have hl : raw241step0Labels = raw241Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw241 raw241Labels permutation32 permutation5
    _ = mixedMoment B node339 node339Labels := by rfl

def raw242 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 3, -2]]
def raw242Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw242step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw242step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw242 raw242Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw242 raw242Labels = mixedMoment B raw242step0 raw242step0Labels := by
      have ha : raw242step0 = (fun i j => raw242 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw242step0 raw242; decide +kernel
      have hl : raw242step0Labels = raw242Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw242 raw242Labels permutation8 permutation5
    mixedMoment B raw242step0 raw242step0Labels = mixedMoment B raw242step1 raw242step1Labels := by
      have ha : raw242step1 = raw242step0 := by apply Matrix.ext; unfold raw242step1 raw242step0; decide +kernel
      have hl : raw242step0Labels = labelEmbedding1 ∘ raw242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw242step0 raw242step0Labels raw242step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw243 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 3, -2]]
def raw243Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw243step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw243step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw243step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw243 raw243Labels = mixedMoment B node341 node341Labels := by
  calc
    mixedMoment B raw243 raw243Labels = mixedMoment B raw243step0 raw243step0Labels := by
      have ha : raw243step0 = (fun i j => raw243 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw243step0 raw243; decide +kernel
      have hl : raw243step0Labels = raw243Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw243 raw243Labels permutation31 permutation4
    mixedMoment B raw243step0 raw243step0Labels = mixedMoment B raw243step1 raw243step1Labels := by
      have ha : raw243step1 = -raw243step0 := by apply Matrix.ext; change ∀ i j, raw243step1 i j = -(raw243step0 i j); unfold raw243step1 raw243step0; decide +kernel
      have hl : raw243step1Labels = raw243step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node341 node341Labels := by rfl

def raw244 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 3, -3]]
def raw244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw244step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw244step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw244 raw244Labels = mixedMoment B node2602 node2602Labels := by
  calc
    mixedMoment B raw244 raw244Labels = mixedMoment B raw244step0 raw244step0Labels := by
      have ha : raw244step0 = (fun i j => raw244 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw244step0 raw244; decide +kernel
      have hl : raw244step0Labels = raw244Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw244 raw244Labels permutation8 permutation5
    mixedMoment B raw244step0 raw244step0Labels = mixedMoment B raw244step1 raw244step1Labels := by
      have ha : raw244step1 = raw244step0 := by apply Matrix.ext; unfold raw244step1 raw244step0; decide +kernel
      have hl : raw244step0Labels = labelEmbedding1 ∘ raw244step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw244step0 raw244step0Labels raw244step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2602 node2602Labels := by rfl

def raw245 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 3, -3]]
def raw245Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw245step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw245step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw245 raw245Labels = mixedMoment B node249 node249Labels := by
  calc
    mixedMoment B raw245 raw245Labels = mixedMoment B raw245step0 raw245step0Labels := by
      have ha : raw245step0 = (fun i j => raw245 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw245step0 raw245; decide +kernel
      have hl : raw245step0Labels = raw245Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw245 raw245Labels permutation31 permutation4
    mixedMoment B raw245step0 raw245step0Labels = mixedMoment B raw245step1 raw245step1Labels := by
      have ha : raw245step1 = -raw245step0 := by apply Matrix.ext; change ∀ i j, raw245step1 i j = -(raw245step0 i j); unfold raw245step1 raw245step0; decide +kernel
      have hl : raw245step1Labels = raw245step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node249 node249Labels := by rfl

def raw246 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 2, -2], ![-2, 2, 0]]
def raw246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw246step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw246step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw246 raw246Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw246 raw246Labels = mixedMoment B raw246step0 raw246step0Labels := by
      have ha : raw246step0 = (fun i j => raw246 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw246step0 raw246; decide +kernel
      have hl : raw246step0Labels = raw246Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw246 raw246Labels permutation8 permutation5
    mixedMoment B raw246step0 raw246step0Labels = mixedMoment B raw246step1 raw246step1Labels := by
      have ha : raw246step1 = raw246step0 := by apply Matrix.ext; unfold raw246step1 raw246step0; decide +kernel
      have hl : raw246step0Labels = labelEmbedding1 ∘ raw246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw246step0 raw246step0Labels raw246step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw247 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 2, -2], ![-2, 2, 0]]
def raw247Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw247step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw247step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw247 raw247Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw247 raw247Labels = mixedMoment B raw247step0 raw247step0Labels := by
      have ha : raw247step0 = (fun i j => raw247 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw247step0 raw247; decide +kernel
      have hl : raw247step0Labels = raw247Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw247 raw247Labels permutation8 permutation5
    _ = mixedMoment B node343 node343Labels := by rfl

def raw248 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw248step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw248step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw248 raw248Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw248 raw248Labels = mixedMoment B raw248step0 raw248step0Labels := by
      have ha : raw248step0 = (fun i j => raw248 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw248step0 raw248; decide +kernel
      have hl : raw248step0Labels = raw248Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw248 raw248Labels permutation8 permutation5
    mixedMoment B raw248step0 raw248step0Labels = mixedMoment B raw248step1 raw248step1Labels := by
      have ha : raw248step1 = raw248step0 := by apply Matrix.ext; unfold raw248step1 raw248step0; decide +kernel
      have hl : raw248step0Labels = labelEmbedding1 ∘ raw248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw248step0 raw248step0Labels raw248step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2605 node2605Labels := by rfl

def raw249 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw249Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw249step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw249step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw249 raw249Labels = mixedMoment B node344 node344Labels := by
  calc
    mixedMoment B raw249 raw249Labels = mixedMoment B raw249step0 raw249step0Labels := by
      have ha : raw249step0 = (fun i j => raw249 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw249step0 raw249; decide +kernel
      have hl : raw249step0Labels = raw249Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw249 raw249Labels permutation8 permutation5
    _ = mixedMoment B node344 node344Labels := by rfl

def raw250 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw250step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw250 raw250Labels = mixedMoment B node2626 node2626Labels := by
  calc
    mixedMoment B raw250 raw250Labels = mixedMoment B raw250step0 raw250step0Labels := by
      have ha : raw250step0 = (fun i j => raw250 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw250step0 raw250; decide +kernel
      have hl : raw250step0Labels = raw250Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw250 raw250Labels permutation32 permutation5
    mixedMoment B raw250step0 raw250step0Labels = mixedMoment B raw250step1 raw250step1Labels := by
      have ha : raw250step1 = raw250step0 := by apply Matrix.ext; unfold raw250step1 raw250step0; decide +kernel
      have hl : raw250step0Labels = labelEmbedding1 ∘ raw250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw250step0 raw250step0Labels raw250step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2626 node2626Labels := by rfl

def raw251 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw251Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw251step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw251step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw251 raw251Labels = mixedMoment B node201 node201Labels := by
  calc
    mixedMoment B raw251 raw251Labels = mixedMoment B raw251step0 raw251step0Labels := by
      have ha : raw251step0 = (fun i j => raw251 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw251step0 raw251; decide +kernel
      have hl : raw251step0Labels = raw251Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw251 raw251Labels permutation151 permutation4
    mixedMoment B raw251step0 raw251step0Labels = mixedMoment B raw251step1 raw251step1Labels := by
      have ha : raw251step1 = -raw251step0 := by apply Matrix.ext; change ∀ i j, raw251step1 i j = -(raw251step0 i j); unfold raw251step1 raw251step0; decide +kernel
      have hl : raw251step1Labels = raw251step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node201 node201Labels := by rfl

def raw252 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw252step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw252 raw252Labels = mixedMoment B node2636 node2636Labels := by
  calc
    mixedMoment B raw252 raw252Labels = mixedMoment B raw252step0 raw252step0Labels := by
      have ha : raw252step0 = (fun i j => raw252 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw252step0 raw252; decide +kernel
      have hl : raw252step0Labels = raw252Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw252 raw252Labels permutation152 permutation5
    mixedMoment B raw252step0 raw252step0Labels = mixedMoment B raw252step1 raw252step1Labels := by
      have ha : raw252step1 = raw252step0 := by apply Matrix.ext; unfold raw252step1 raw252step0; decide +kernel
      have hl : raw252step0Labels = labelEmbedding1 ∘ raw252step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw252step0 raw252step0Labels raw252step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2636 node2636Labels := by rfl

def raw253 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw253Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw253step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw253 raw253Labels = mixedMoment B node351 node351Labels := by
  calc
    mixedMoment B raw253 raw253Labels = mixedMoment B raw253step0 raw253step0Labels := by
      have ha : raw253step0 = (fun i j => raw253 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw253step0 raw253; decide +kernel
      have hl : raw253step0Labels = raw253Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw253 raw253Labels permutation152 permutation5
    _ = mixedMoment B node351 node351Labels := by rfl

def raw254 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw254 raw254Labels = mixedMoment B node2637 node2637Labels := by
  calc
    mixedMoment B raw254 raw254Labels = mixedMoment B raw254step0 raw254step0Labels := by
      have ha : raw254step0 = (fun i j => raw254 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw254step0 raw254; decide +kernel
      have hl : raw254step0Labels = raw254Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw254 raw254Labels permutation32 permutation5
    mixedMoment B raw254step0 raw254step0Labels = mixedMoment B raw254step1 raw254step1Labels := by
      have ha : raw254step1 = raw254step0 := by apply Matrix.ext; unfold raw254step1 raw254step0; decide +kernel
      have hl : raw254step0Labels = labelEmbedding1 ∘ raw254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw254step0 raw254step0Labels raw254step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2637 node2637Labels := by rfl

def raw255 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw255Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw255step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw255 raw255Labels = mixedMoment B node352 node352Labels := by
  calc
    mixedMoment B raw255 raw255Labels = mixedMoment B raw255step0 raw255step0Labels := by
      have ha : raw255step0 = (fun i j => raw255 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw255step0 raw255; decide +kernel
      have hl : raw255step0Labels = raw255Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw255 raw255Labels permutation32 permutation5
    _ = mixedMoment B node352 node352Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
