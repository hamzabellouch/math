import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw0step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw0step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw0step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw0step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical0 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw0 raw0Labels = mixedMoment B node644 node644Labels := by
  calc
    mixedMoment B raw0 raw0Labels = mixedMoment B raw0step0 raw0step0Labels := by
      have ha : raw0step0 = (fun i j => raw0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw0step0 raw0; decide +kernel
      have hl : raw0step0Labels = raw0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw0 raw0Labels permutation32 permutation5
    mixedMoment B raw0step0 raw0step0Labels = mixedMoment B raw0step1 raw0step1Labels := by
      have ha : raw0step1 = raw0step0 := by apply Matrix.ext; unfold raw0step1 raw0step0; decide +kernel
      have hl : raw0step0Labels = labelEmbedding1 ∘ raw0step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw0step0 raw0step0Labels raw0step1Labels labelEmbedding1 hl
    _ = mixedMoment B node644 node644Labels := by rfl

def raw1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw1step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical1 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1 raw1Labels = mixedMoment B node26 node26Labels := by
  calc
    mixedMoment B raw1 raw1Labels = mixedMoment B raw1step0 raw1step0Labels := by
      have ha : raw1step0 = (fun i j => raw1 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1step0 raw1; decide +kernel
      have hl : raw1step0Labels = raw1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1 raw1Labels permutation44 permutation4
    _ = mixedMoment B node26 node26Labels := by rfl

def raw2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw2step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2 raw2Labels = mixedMoment B node645 node645Labels := by
  calc
    mixedMoment B raw2 raw2Labels = mixedMoment B raw2step0 raw2step0Labels := by
      have ha : raw2step0 = (fun i j => raw2 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2step0 raw2; decide +kernel
      have hl : raw2step0Labels = raw2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2 raw2Labels permutation8 permutation5
    mixedMoment B raw2step0 raw2step0Labels = mixedMoment B raw2step1 raw2step1Labels := by
      have ha : raw2step1 = raw2step0 := by apply Matrix.ext; unfold raw2step1 raw2step0; decide +kernel
      have hl : raw2step0Labels = labelEmbedding1 ∘ raw2step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2step0 raw2step0Labels raw2step1Labels labelEmbedding1 hl
    _ = mixedMoment B node645 node645Labels := by rfl

def raw3 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw3step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw3step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical3 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3 raw3Labels = mixedMoment B node31 node31Labels := by
  calc
    mixedMoment B raw3 raw3Labels = mixedMoment B raw3step0 raw3step0Labels := by
      have ha : raw3step0 = (fun i j => raw3 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3step0 raw3; decide +kernel
      have hl : raw3step0Labels = raw3Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3 raw3Labels permutation8 permutation4
    _ = mixedMoment B node31 node31Labels := by rfl

def raw4 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw4Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4 raw4Labels = mixedMoment B node646 node646Labels := by
  calc
    mixedMoment B raw4 raw4Labels = mixedMoment B raw4step0 raw4step0Labels := by
      have ha : raw4step0 = (fun i j => raw4 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4step0 raw4; decide +kernel
      have hl : raw4step0Labels = raw4Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4 raw4Labels permutation32 permutation5
    mixedMoment B raw4step0 raw4step0Labels = mixedMoment B raw4step1 raw4step1Labels := by
      have ha : raw4step1 = raw4step0 := by apply Matrix.ext; unfold raw4step1 raw4step0; decide +kernel
      have hl : raw4step0Labels = labelEmbedding1 ∘ raw4step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4step0 raw4step0Labels raw4step1Labels labelEmbedding1 hl
    _ = mixedMoment B node646 node646Labels := by rfl

def raw5 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw5Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw5step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical5 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5 raw5Labels = mixedMoment B node23 node23Labels := by
  calc
    mixedMoment B raw5 raw5Labels = mixedMoment B raw5step0 raw5step0Labels := by
      have ha : raw5step0 = (fun i j => raw5 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5step0 raw5; decide +kernel
      have hl : raw5step0Labels = raw5Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5 raw5Labels permutation40 permutation4
    _ = mixedMoment B node23 node23Labels := by rfl

def raw6 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw6Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw6step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw6step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6 raw6Labels = mixedMoment B node647 node647Labels := by
  calc
    mixedMoment B raw6 raw6Labels = mixedMoment B raw6step0 raw6step0Labels := by
      have ha : raw6step0 = (fun i j => raw6 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6step0 raw6; decide +kernel
      have hl : raw6step0Labels = raw6Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6 raw6Labels permutation8 permutation5
    mixedMoment B raw6step0 raw6step0Labels = mixedMoment B raw6step1 raw6step1Labels := by
      have ha : raw6step1 = raw6step0 := by apply Matrix.ext; unfold raw6step1 raw6step0; decide +kernel
      have hl : raw6step0Labels = labelEmbedding1 ∘ raw6step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6step0 raw6step0Labels raw6step1Labels labelEmbedding1 hl
    _ = mixedMoment B node647 node647Labels := by rfl

def raw7 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw7Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw7step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw7step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical7 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7 raw7Labels = mixedMoment B node28 node28Labels := by
  calc
    mixedMoment B raw7 raw7Labels = mixedMoment B raw7step0 raw7step0Labels := by
      have ha : raw7step0 = (fun i j => raw7 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7step0 raw7; decide +kernel
      have hl : raw7step0Labels = raw7Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7 raw7Labels permutation10 permutation4
    _ = mixedMoment B node28 node28Labels := by rfl

def raw8 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw8Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw8step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw8step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8 raw8Labels = mixedMoment B node648 node648Labels := by
  calc
    mixedMoment B raw8 raw8Labels = mixedMoment B raw8step0 raw8step0Labels := by
      have ha : raw8step0 = (fun i j => raw8 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8step0 raw8; decide +kernel
      have hl : raw8step0Labels = raw8Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8 raw8Labels permutation8 permutation5
    mixedMoment B raw8step0 raw8step0Labels = mixedMoment B raw8step1 raw8step1Labels := by
      have ha : raw8step1 = raw8step0 := by apply Matrix.ext; unfold raw8step1 raw8step0; decide +kernel
      have hl : raw8step0Labels = labelEmbedding1 ∘ raw8step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8step0 raw8step0Labels raw8step1Labels labelEmbedding1 hl
    _ = mixedMoment B node648 node648Labels := by rfl

def raw9 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw9Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw9step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical9 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9 raw9Labels = mixedMoment B node33 node33Labels := by
  calc
    mixedMoment B raw9 raw9Labels = mixedMoment B raw9step0 raw9step0Labels := by
      have ha : raw9step0 = (fun i j => raw9 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9step0 raw9; decide +kernel
      have hl : raw9step0Labels = raw9Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9 raw9Labels permutation9 permutation4
    _ = mixedMoment B node33 node33Labels := by rfl

def raw10 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw10Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10 raw10Labels = mixedMoment B node649 node649Labels := by
  calc
    mixedMoment B raw10 raw10Labels = mixedMoment B raw10step0 raw10step0Labels := by
      have ha : raw10step0 = (fun i j => raw10 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10step0 raw10; decide +kernel
      have hl : raw10step0Labels = raw10Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10 raw10Labels permutation8 permutation5
    mixedMoment B raw10step0 raw10step0Labels = mixedMoment B raw10step1 raw10step1Labels := by
      have ha : raw10step1 = raw10step0 := by apply Matrix.ext; unfold raw10step1 raw10step0; decide +kernel
      have hl : raw10step0Labels = labelEmbedding1 ∘ raw10step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10step0 raw10step0Labels raw10step1Labels labelEmbedding1 hl
    _ = mixedMoment B node649 node649Labels := by rfl

def raw11 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw11Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw11step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw11step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical11 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11 raw11Labels = mixedMoment B node34 node34Labels := by
  calc
    mixedMoment B raw11 raw11Labels = mixedMoment B raw11step0 raw11step0Labels := by
      have ha : raw11step0 = (fun i j => raw11 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11step0 raw11; decide +kernel
      have hl : raw11step0Labels = raw11Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11 raw11Labels permutation8 permutation4
    _ = mixedMoment B node34 node34Labels := by rfl

def raw12 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 4, -2]]
def raw12Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw12step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw12step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12 raw12Labels = mixedMoment B node650 node650Labels := by
  calc
    mixedMoment B raw12 raw12Labels = mixedMoment B raw12step0 raw12step0Labels := by
      have ha : raw12step0 = (fun i j => raw12 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12step0 raw12; decide +kernel
      have hl : raw12step0Labels = raw12Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12 raw12Labels permutation2 permutation5
    mixedMoment B raw12step0 raw12step0Labels = mixedMoment B raw12step1 raw12step1Labels := by
      have ha : raw12step1 = raw12step0 := by apply Matrix.ext; unfold raw12step1 raw12step0; decide +kernel
      have hl : raw12step0Labels = labelEmbedding1 ∘ raw12step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12step0 raw12step0Labels raw12step1Labels labelEmbedding1 hl
    _ = mixedMoment B node650 node650Labels := by rfl

def raw13 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 4, -2]]
def raw13Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw13step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw13step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical13 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13 raw13Labels = mixedMoment B node35 node35Labels := by
  calc
    mixedMoment B raw13 raw13Labels = mixedMoment B raw13step0 raw13step0Labels := by
      have ha : raw13step0 = (fun i j => raw13 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13step0 raw13; decide +kernel
      have hl : raw13step0Labels = raw13Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13 raw13Labels permutation2 permutation4
    _ = mixedMoment B node35 node35Labels := by rfl

def raw14 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw14Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw14step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw14step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14 raw14Labels = mixedMoment B node652 node652Labels := by
  calc
    mixedMoment B raw14 raw14Labels = mixedMoment B raw14step0 raw14step0Labels := by
      have ha : raw14step0 = (fun i j => raw14 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14step0 raw14; decide +kernel
      have hl : raw14step0Labels = raw14Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14 raw14Labels permutation8 permutation5
    mixedMoment B raw14step0 raw14step0Labels = mixedMoment B raw14step1 raw14step1Labels := by
      have ha : raw14step1 = raw14step0 := by apply Matrix.ext; unfold raw14step1 raw14step0; decide +kernel
      have hl : raw14step0Labels = labelEmbedding1 ∘ raw14step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14step0 raw14step0Labels raw14step1Labels labelEmbedding1 hl
    _ = mixedMoment B node652 node652Labels := by rfl

def raw15 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw15Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw15step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw15step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical15 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15 raw15Labels = mixedMoment B node25 node25Labels := by
  calc
    mixedMoment B raw15 raw15Labels = mixedMoment B raw15step0 raw15step0Labels := by
      have ha : raw15step0 = (fun i j => raw15 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15step0 raw15; decide +kernel
      have hl : raw15step0Labels = raw15Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15 raw15Labels permutation8 permutation4
    _ = mixedMoment B node25 node25Labels := by rfl

def raw16 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 2, 0], ![0, 3, -3]]
def raw16Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw16step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw16step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16 raw16Labels = mixedMoment B node655 node655Labels := by
  calc
    mixedMoment B raw16 raw16Labels = mixedMoment B raw16step0 raw16step0Labels := by
      have ha : raw16step0 = (fun i j => raw16 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16step0 raw16; decide +kernel
      have hl : raw16step0Labels = raw16Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16 raw16Labels permutation2 permutation5
    mixedMoment B raw16step0 raw16step0Labels = mixedMoment B raw16step1 raw16step1Labels := by
      have ha : raw16step1 = raw16step0 := by apply Matrix.ext; unfold raw16step1 raw16step0; decide +kernel
      have hl : raw16step0Labels = labelEmbedding1 ∘ raw16step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16step0 raw16step0Labels raw16step1Labels labelEmbedding1 hl
    _ = mixedMoment B node655 node655Labels := by rfl

def raw17 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 2, 0], ![0, 3, -3]]
def raw17Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw17step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw17step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical17 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17 raw17Labels = mixedMoment B node38 node38Labels := by
  calc
    mixedMoment B raw17 raw17Labels = mixedMoment B raw17step0 raw17step0Labels := by
      have ha : raw17step0 = (fun i j => raw17 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17step0 raw17; decide +kernel
      have hl : raw17step0Labels = raw17Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17 raw17Labels permutation2 permutation4
    _ = mixedMoment B node38 node38Labels := by rfl

def raw18 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw18Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18 raw18Labels = mixedMoment B node1161 node1161Labels := by
  calc
    mixedMoment B raw18 raw18Labels = mixedMoment B raw18step0 raw18step0Labels := by
      have ha : raw18step0 = (fun i j => raw18 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18step0 raw18; decide +kernel
      have hl : raw18step0Labels = raw18Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18 raw18Labels permutation152 permutation5
    mixedMoment B raw18step0 raw18step0Labels = mixedMoment B raw18step1 raw18step1Labels := by
      have ha : raw18step1 = raw18step0 := by apply Matrix.ext; unfold raw18step1 raw18step0; decide +kernel
      have hl : raw18step0Labels = labelEmbedding1 ∘ raw18step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18step0 raw18step0Labels raw18step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1161 node1161Labels := by rfl

def raw19 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw19Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw19step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical19 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19 raw19Labels = mixedMoment B node125 node125Labels := by
  calc
    mixedMoment B raw19 raw19Labels = mixedMoment B raw19step0 raw19step0Labels := by
      have ha : raw19step0 = (fun i j => raw19 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19step0 raw19; decide +kernel
      have hl : raw19step0Labels = raw19Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19 raw19Labels permutation152 permutation4
    _ = mixedMoment B node125 node125Labels := by rfl

def raw20 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw20Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20 raw20Labels = mixedMoment B node1162 node1162Labels := by
  calc
    mixedMoment B raw20 raw20Labels = mixedMoment B raw20step0 raw20step0Labels := by
      have ha : raw20step0 = (fun i j => raw20 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20step0 raw20; decide +kernel
      have hl : raw20step0Labels = raw20Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20 raw20Labels permutation152 permutation5
    mixedMoment B raw20step0 raw20step0Labels = mixedMoment B raw20step1 raw20step1Labels := by
      have ha : raw20step1 = raw20step0 := by apply Matrix.ext; unfold raw20step1 raw20step0; decide +kernel
      have hl : raw20step0Labels = labelEmbedding1 ∘ raw20step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20step0 raw20step0Labels raw20step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1162 node1162Labels := by rfl

def raw21 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw21Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw21step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw21step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical21 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21 raw21Labels = mixedMoment B node120 node120Labels := by
  calc
    mixedMoment B raw21 raw21Labels = mixedMoment B raw21step0 raw21step0Labels := by
      have ha : raw21step0 = (fun i j => raw21 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21step0 raw21; decide +kernel
      have hl : raw21step0Labels = raw21Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21 raw21Labels permutation164 permutation4
    _ = mixedMoment B node120 node120Labels := by rfl

def raw22 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw22Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22 raw22Labels = mixedMoment B node1163 node1163Labels := by
  calc
    mixedMoment B raw22 raw22Labels = mixedMoment B raw22step0 raw22step0Labels := by
      have ha : raw22step0 = (fun i j => raw22 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22step0 raw22; decide +kernel
      have hl : raw22step0Labels = raw22Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22 raw22Labels permutation32 permutation5
    mixedMoment B raw22step0 raw22step0Labels = mixedMoment B raw22step1 raw22step1Labels := by
      have ha : raw22step1 = raw22step0 := by apply Matrix.ext; unfold raw22step1 raw22step0; decide +kernel
      have hl : raw22step0Labels = labelEmbedding1 ∘ raw22step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22step0 raw22step0Labels raw22step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1163 node1163Labels := by rfl

def raw23 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw23Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw23step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical23 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23 raw23Labels = mixedMoment B node126 node126Labels := by
  calc
    mixedMoment B raw23 raw23Labels = mixedMoment B raw23step0 raw23step0Labels := by
      have ha : raw23step0 = (fun i j => raw23 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23step0 raw23; decide +kernel
      have hl : raw23step0Labels = raw23Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23 raw23Labels permutation32 permutation4
    _ = mixedMoment B node126 node126Labels := by rfl

def raw24 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw24Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24 raw24Labels = mixedMoment B node1164 node1164Labels := by
  calc
    mixedMoment B raw24 raw24Labels = mixedMoment B raw24step0 raw24step0Labels := by
      have ha : raw24step0 = (fun i j => raw24 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24step0 raw24; decide +kernel
      have hl : raw24step0Labels = raw24Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24 raw24Labels permutation152 permutation5
    mixedMoment B raw24step0 raw24step0Labels = mixedMoment B raw24step1 raw24step1Labels := by
      have ha : raw24step1 = raw24step0 := by apply Matrix.ext; unfold raw24step1 raw24step0; decide +kernel
      have hl : raw24step0Labels = labelEmbedding1 ∘ raw24step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24step0 raw24step0Labels raw24step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1164 node1164Labels := by rfl

def raw25 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw25Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw25step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical25 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25 raw25Labels = mixedMoment B node118 node118Labels := by
  calc
    mixedMoment B raw25 raw25Labels = mixedMoment B raw25step0 raw25step0Labels := by
      have ha : raw25step0 = (fun i j => raw25 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25step0 raw25; decide +kernel
      have hl : raw25step0Labels = raw25Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25 raw25Labels permutation160 permutation4
    _ = mixedMoment B node118 node118Labels := by rfl

def raw26 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw26Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw26step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw26step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26 raw26Labels = mixedMoment B node1165 node1165Labels := by
  calc
    mixedMoment B raw26 raw26Labels = mixedMoment B raw26step0 raw26step0Labels := by
      have ha : raw26step0 = (fun i j => raw26 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26step0 raw26; decide +kernel
      have hl : raw26step0Labels = raw26Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26 raw26Labels permutation32 permutation5
    mixedMoment B raw26step0 raw26step0Labels = mixedMoment B raw26step1 raw26step1Labels := by
      have ha : raw26step1 = raw26step0 := by apply Matrix.ext; unfold raw26step1 raw26step0; decide +kernel
      have hl : raw26step0Labels = labelEmbedding1 ∘ raw26step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26step0 raw26step0Labels raw26step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1165 node1165Labels := by rfl

def raw27 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw27Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw27step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical27 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27 raw27Labels = mixedMoment B node121 node121Labels := by
  calc
    mixedMoment B raw27 raw27Labels = mixedMoment B raw27step0 raw27step0Labels := by
      have ha : raw27step0 = (fun i j => raw27 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27step0 raw27; decide +kernel
      have hl : raw27step0Labels = raw27Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27 raw27Labels permutation34 permutation4
    _ = mixedMoment B node121 node121Labels := by rfl

def raw28 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw28Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw28step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw28step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28 raw28Labels = mixedMoment B node1166 node1166Labels := by
  calc
    mixedMoment B raw28 raw28Labels = mixedMoment B raw28step0 raw28step0Labels := by
      have ha : raw28step0 = (fun i j => raw28 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28step0 raw28; decide +kernel
      have hl : raw28step0Labels = raw28Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28 raw28Labels permutation32 permutation5
    mixedMoment B raw28step0 raw28step0Labels = mixedMoment B raw28step1 raw28step1Labels := by
      have ha : raw28step1 = raw28step0 := by apply Matrix.ext; unfold raw28step1 raw28step0; decide +kernel
      have hl : raw28step0Labels = labelEmbedding1 ∘ raw28step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28step0 raw28step0Labels raw28step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1166 node1166Labels := by rfl

def raw29 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw29Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw29step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical29 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29 raw29Labels = mixedMoment B node127 node127Labels := by
  calc
    mixedMoment B raw29 raw29Labels = mixedMoment B raw29step0 raw29step0Labels := by
      have ha : raw29step0 = (fun i j => raw29 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29step0 raw29; decide +kernel
      have hl : raw29step0Labels = raw29Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29 raw29Labels permutation33 permutation4
    _ = mixedMoment B node127 node127Labels := by rfl

def raw30 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw30Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30 raw30Labels = mixedMoment B node1167 node1167Labels := by
  calc
    mixedMoment B raw30 raw30Labels = mixedMoment B raw30step0 raw30step0Labels := by
      have ha : raw30step0 = (fun i j => raw30 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30step0 raw30; decide +kernel
      have hl : raw30step0Labels = raw30Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30 raw30Labels permutation32 permutation5
    mixedMoment B raw30step0 raw30step0Labels = mixedMoment B raw30step1 raw30step1Labels := by
      have ha : raw30step1 = raw30step0 := by apply Matrix.ext; unfold raw30step1 raw30step0; decide +kernel
      have hl : raw30step0Labels = labelEmbedding1 ∘ raw30step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30step0 raw30step0Labels raw30step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1167 node1167Labels := by rfl

def raw31 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw31Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw31step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical31 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31 raw31Labels = mixedMoment B node128 node128Labels := by
  calc
    mixedMoment B raw31 raw31Labels = mixedMoment B raw31step0 raw31step0Labels := by
      have ha : raw31step0 = (fun i j => raw31 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31step0 raw31; decide +kernel
      have hl : raw31step0Labels = raw31Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31 raw31Labels permutation32 permutation4
    _ = mixedMoment B node128 node128Labels := by rfl

def raw32 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 4, -2]]
def raw32Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw32step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw32step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32 raw32Labels = mixedMoment B node1168 node1168Labels := by
  calc
    mixedMoment B raw32 raw32Labels = mixedMoment B raw32step0 raw32step0Labels := by
      have ha : raw32step0 = (fun i j => raw32 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32step0 raw32; decide +kernel
      have hl : raw32step0Labels = raw32Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32 raw32Labels permutation8 permutation5
    mixedMoment B raw32step0 raw32step0Labels = mixedMoment B raw32step1 raw32step1Labels := by
      have ha : raw32step1 = raw32step0 := by apply Matrix.ext; unfold raw32step1 raw32step0; decide +kernel
      have hl : raw32step0Labels = labelEmbedding1 ∘ raw32step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32step0 raw32step0Labels raw32step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1168 node1168Labels := by rfl

def raw33 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 4, -2]]
def raw33Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw33step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw33step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical33 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33 raw33Labels = mixedMoment B node129 node129Labels := by
  calc
    mixedMoment B raw33 raw33Labels = mixedMoment B raw33step0 raw33step0Labels := by
      have ha : raw33step0 = (fun i j => raw33 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33step0 raw33; decide +kernel
      have hl : raw33step0Labels = raw33Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33 raw33Labels permutation8 permutation4
    _ = mixedMoment B node129 node129Labels := by rfl

def raw34 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw34Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34 raw34Labels = mixedMoment B node1170 node1170Labels := by
  calc
    mixedMoment B raw34 raw34Labels = mixedMoment B raw34step0 raw34step0Labels := by
      have ha : raw34step0 = (fun i j => raw34 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34step0 raw34; decide +kernel
      have hl : raw34step0Labels = raw34Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34 raw34Labels permutation32 permutation5
    mixedMoment B raw34step0 raw34step0Labels = mixedMoment B raw34step1 raw34step1Labels := by
      have ha : raw34step1 = raw34step0 := by apply Matrix.ext; unfold raw34step1 raw34step0; decide +kernel
      have hl : raw34step0Labels = labelEmbedding1 ∘ raw34step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34step0 raw34step0Labels raw34step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1170 node1170Labels := by rfl

def raw35 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw35Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw35step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw35step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical35 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35 raw35Labels = mixedMoment B node119 node119Labels := by
  calc
    mixedMoment B raw35 raw35Labels = mixedMoment B raw35step0 raw35step0Labels := by
      have ha : raw35step0 = (fun i j => raw35 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35step0 raw35; decide +kernel
      have hl : raw35step0Labels = raw35Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35 raw35Labels permutation32 permutation4
    _ = mixedMoment B node119 node119Labels := by rfl

def raw36 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw36Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36 raw36Labels = mixedMoment B node1172 node1172Labels := by
  calc
    mixedMoment B raw36 raw36Labels = mixedMoment B raw36step0 raw36step0Labels := by
      have ha : raw36step0 = (fun i j => raw36 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36step0 raw36; decide +kernel
      have hl : raw36step0Labels = raw36Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36 raw36Labels permutation32 permutation5
    mixedMoment B raw36step0 raw36step0Labels = mixedMoment B raw36step1 raw36step1Labels := by
      have ha : raw36step1 = raw36step0 := by apply Matrix.ext; unfold raw36step1 raw36step0; decide +kernel
      have hl : raw36step0Labels = labelEmbedding1 ∘ raw36step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36step0 raw36step0Labels raw36step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1172 node1172Labels := by rfl

def raw37 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw37Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37 raw37Labels = mixedMoment B node124 node124Labels := by
  calc
    mixedMoment B raw37 raw37Labels = mixedMoment B raw37step0 raw37step0Labels := by
      have ha : raw37step0 = (fun i j => raw37 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37step0 raw37; decide +kernel
      have hl : raw37step0Labels = raw37Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37 raw37Labels permutation33 permutation4
    _ = mixedMoment B node124 node124Labels := by rfl

def raw38 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 4, -3]]
def raw38Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw38step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw38step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw38step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw38step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38 raw38Labels = mixedMoment B node1173 node1173Labels := by
  calc
    mixedMoment B raw38 raw38Labels = mixedMoment B raw38step0 raw38step0Labels := by
      have ha : raw38step0 = (fun i j => raw38 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38step0 raw38; decide +kernel
      have hl : raw38step0Labels = raw38Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38 raw38Labels permutation8 permutation5
    mixedMoment B raw38step0 raw38step0Labels = mixedMoment B raw38step1 raw38step1Labels := by
      have ha : raw38step1 = raw38step0 := by apply Matrix.ext; unfold raw38step1 raw38step0; decide +kernel
      have hl : raw38step0Labels = labelEmbedding1 ∘ raw38step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38step0 raw38step0Labels raw38step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1173 node1173Labels := by rfl

def raw39 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 4, -3]]
def raw39Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw39step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw39step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39 raw39Labels = mixedMoment B node70 node70Labels := by
  calc
    mixedMoment B raw39 raw39Labels = mixedMoment B raw39step0 raw39step0Labels := by
      have ha : raw39step0 = (fun i j => raw39 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39step0 raw39; decide +kernel
      have hl : raw39step0Labels = raw39Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39 raw39Labels permutation31 permutation4
    mixedMoment B raw39step0 raw39step0Labels = mixedMoment B raw39step1 raw39step1Labels := by
      have ha : raw39step1 = -raw39step0 := by apply Matrix.ext; change ∀ i j, raw39step1 i j = -(raw39step0 i j); unfold raw39step1 raw39step0; decide +kernel
      have hl : raw39step1Labels = raw39step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node70 node70Labels := by rfl

def raw40 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw40Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw40step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw40step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw40step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw40step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40 raw40Labels = mixedMoment B node1175 node1175Labels := by
  calc
    mixedMoment B raw40 raw40Labels = mixedMoment B raw40step0 raw40step0Labels := by
      have ha : raw40step0 = (fun i j => raw40 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw40step0 raw40; decide +kernel
      have hl : raw40step0Labels = raw40Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40 raw40Labels permutation8 permutation5
    mixedMoment B raw40step0 raw40step0Labels = mixedMoment B raw40step1 raw40step1Labels := by
      have ha : raw40step1 = raw40step0 := by apply Matrix.ext; unfold raw40step1 raw40step0; decide +kernel
      have hl : raw40step0Labels = labelEmbedding1 ∘ raw40step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw40step0 raw40step0Labels raw40step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1175 node1175Labels := by rfl

def raw41 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw41Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw41step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical41 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41 raw41Labels = mixedMoment B node133 node133Labels := by
  calc
    mixedMoment B raw41 raw41Labels = mixedMoment B raw41step0 raw41step0Labels := by
      have ha : raw41step0 = (fun i j => raw41 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41step0 raw41; decide +kernel
      have hl : raw41step0Labels = raw41Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41 raw41Labels permutation8 permutation4
    _ = mixedMoment B node133 node133Labels := by rfl

def raw42 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw42Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw42step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw42step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw42step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42 raw42Labels = mixedMoment B node1176 node1176Labels := by
  calc
    mixedMoment B raw42 raw42Labels = mixedMoment B raw42step0 raw42step0Labels := by
      have ha : raw42step0 = (fun i j => raw42 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42step0 raw42; decide +kernel
      have hl : raw42step0Labels = raw42Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42 raw42Labels permutation8 permutation5
    mixedMoment B raw42step0 raw42step0Labels = mixedMoment B raw42step1 raw42step1Labels := by
      have ha : raw42step1 = raw42step0 := by apply Matrix.ext; unfold raw42step1 raw42step0; decide +kernel
      have hl : raw42step0Labels = labelEmbedding1 ∘ raw42step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42step0 raw42step0Labels raw42step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1176 node1176Labels := by rfl

def raw43 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw43Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw43step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw43step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical43 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43 raw43Labels = mixedMoment B node132 node132Labels := by
  calc
    mixedMoment B raw43 raw43Labels = mixedMoment B raw43step0 raw43step0Labels := by
      have ha : raw43step0 = (fun i j => raw43 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43step0 raw43; decide +kernel
      have hl : raw43step0Labels = raw43Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43 raw43Labels permutation8 permutation4
    _ = mixedMoment B node132 node132Labels := by rfl

def raw44 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw44Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw44step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw44step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw44step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw44step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical44 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw44 raw44Labels = mixedMoment B node1177 node1177Labels := by
  calc
    mixedMoment B raw44 raw44Labels = mixedMoment B raw44step0 raw44step0Labels := by
      have ha : raw44step0 = (fun i j => raw44 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw44step0 raw44; decide +kernel
      have hl : raw44step0Labels = raw44Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw44 raw44Labels permutation8 permutation5
    mixedMoment B raw44step0 raw44step0Labels = mixedMoment B raw44step1 raw44step1Labels := by
      have ha : raw44step1 = raw44step0 := by apply Matrix.ext; unfold raw44step1 raw44step0; decide +kernel
      have hl : raw44step0Labels = labelEmbedding1 ∘ raw44step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw44step0 raw44step0Labels raw44step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1177 node1177Labels := by rfl

def raw45 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw45Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw45step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw45step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical45 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw45 raw45Labels = mixedMoment B node131 node131Labels := by
  calc
    mixedMoment B raw45 raw45Labels = mixedMoment B raw45step0 raw45step0Labels := by
      have ha : raw45step0 = (fun i j => raw45 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw45step0 raw45; decide +kernel
      have hl : raw45step0Labels = raw45Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw45 raw45Labels permutation8 permutation4
    _ = mixedMoment B node131 node131Labels := by rfl

def raw46 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw46Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw46step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw46step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw46step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw46step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical46 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw46 raw46Labels = mixedMoment B node1251 node1251Labels := by
  calc
    mixedMoment B raw46 raw46Labels = mixedMoment B raw46step0 raw46step0Labels := by
      have ha : raw46step0 = (fun i j => raw46 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw46step0 raw46; decide +kernel
      have hl : raw46step0Labels = raw46Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw46 raw46Labels permutation32 permutation5
    mixedMoment B raw46step0 raw46step0Labels = mixedMoment B raw46step1 raw46step1Labels := by
      have ha : raw46step1 = raw46step0 := by apply Matrix.ext; unfold raw46step1 raw46step0; decide +kernel
      have hl : raw46step0Labels = labelEmbedding1 ∘ raw46step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw46step0 raw46step0Labels raw46step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1251 node1251Labels := by rfl

def raw47 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw47Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw47step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw47step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical47 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw47 raw47Labels = mixedMoment B node137 node137Labels := by
  calc
    mixedMoment B raw47 raw47Labels = mixedMoment B raw47step0 raw47step0Labels := by
      have ha : raw47step0 = (fun i j => raw47 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw47step0 raw47; decide +kernel
      have hl : raw47step0Labels = raw47Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw47 raw47Labels permutation32 permutation4
    _ = mixedMoment B node137 node137Labels := by rfl

def raw48 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw48Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw48step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw48step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw48step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw48step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical48 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw48 raw48Labels = mixedMoment B node1254 node1254Labels := by
  calc
    mixedMoment B raw48 raw48Labels = mixedMoment B raw48step0 raw48step0Labels := by
      have ha : raw48step0 = (fun i j => raw48 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw48step0 raw48; decide +kernel
      have hl : raw48step0Labels = raw48Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw48 raw48Labels permutation32 permutation5
    mixedMoment B raw48step0 raw48step0Labels = mixedMoment B raw48step1 raw48step1Labels := by
      have ha : raw48step1 = raw48step0 := by apply Matrix.ext; unfold raw48step1 raw48step0; decide +kernel
      have hl : raw48step0Labels = labelEmbedding1 ∘ raw48step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw48step0 raw48step0Labels raw48step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1254 node1254Labels := by rfl

def raw49 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw49Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw49step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw49step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical49 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw49 raw49Labels = mixedMoment B node138 node138Labels := by
  calc
    mixedMoment B raw49 raw49Labels = mixedMoment B raw49step0 raw49step0Labels := by
      have ha : raw49step0 = (fun i j => raw49 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw49step0 raw49; decide +kernel
      have hl : raw49step0Labels = raw49Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw49 raw49Labels permutation32 permutation4
    _ = mixedMoment B node138 node138Labels := by rfl

def raw50 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 4, -4]]
def raw50Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw50step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw50step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw50step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw50step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical50 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw50 raw50Labels = mixedMoment B node1255 node1255Labels := by
  calc
    mixedMoment B raw50 raw50Labels = mixedMoment B raw50step0 raw50step0Labels := by
      have ha : raw50step0 = (fun i j => raw50 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw50step0 raw50; decide +kernel
      have hl : raw50step0Labels = raw50Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw50 raw50Labels permutation8 permutation5
    mixedMoment B raw50step0 raw50step0Labels = mixedMoment B raw50step1 raw50step1Labels := by
      have ha : raw50step1 = raw50step0 := by apply Matrix.ext; unfold raw50step1 raw50step0; decide +kernel
      have hl : raw50step0Labels = labelEmbedding1 ∘ raw50step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw50step0 raw50step0Labels raw50step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1255 node1255Labels := by rfl

def raw51 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 4, -4]]
def raw51Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw51step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw51step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw51step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw51step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical51 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw51 raw51Labels = mixedMoment B node49 node49Labels := by
  calc
    mixedMoment B raw51 raw51Labels = mixedMoment B raw51step0 raw51step0Labels := by
      have ha : raw51step0 = (fun i j => raw51 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw51step0 raw51; decide +kernel
      have hl : raw51step0Labels = raw51Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw51 raw51Labels permutation29 permutation4
    mixedMoment B raw51step0 raw51step0Labels = mixedMoment B raw51step1 raw51step1Labels := by
      have ha : raw51step1 = -raw51step0 := by apply Matrix.ext; change ∀ i j, raw51step1 i j = -(raw51step0 i j); unfold raw51step1 raw51step0; decide +kernel
      have hl : raw51step1Labels = raw51step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node49 node49Labels := by rfl

def raw52 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw52Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw52step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw52step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw52step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw52step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical52 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw52 raw52Labels = mixedMoment B node1265 node1265Labels := by
  calc
    mixedMoment B raw52 raw52Labels = mixedMoment B raw52step0 raw52step0Labels := by
      have ha : raw52step0 = (fun i j => raw52 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw52step0 raw52; decide +kernel
      have hl : raw52step0Labels = raw52Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw52 raw52Labels permutation152 permutation5
    mixedMoment B raw52step0 raw52step0Labels = mixedMoment B raw52step1 raw52step1Labels := by
      have ha : raw52step1 = raw52step0 := by apply Matrix.ext; unfold raw52step1 raw52step0; decide +kernel
      have hl : raw52step0Labels = labelEmbedding1 ∘ raw52step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw52step0 raw52step0Labels raw52step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1265 node1265Labels := by rfl

def raw53 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw53Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw53step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw53step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical53 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw53 raw53Labels = mixedMoment B node141 node141Labels := by
  calc
    mixedMoment B raw53 raw53Labels = mixedMoment B raw53step0 raw53step0Labels := by
      have ha : raw53step0 = (fun i j => raw53 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw53step0 raw53; decide +kernel
      have hl : raw53step0Labels = raw53Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw53 raw53Labels permutation170 permutation4
    _ = mixedMoment B node141 node141Labels := by rfl

def raw54 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw54Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw54step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw54step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw54step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw54step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical54 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw54 raw54Labels = mixedMoment B node1266 node1266Labels := by
  calc
    mixedMoment B raw54 raw54Labels = mixedMoment B raw54step0 raw54step0Labels := by
      have ha : raw54step0 = (fun i j => raw54 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw54step0 raw54; decide +kernel
      have hl : raw54step0Labels = raw54Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw54 raw54Labels permutation32 permutation5
    mixedMoment B raw54step0 raw54step0Labels = mixedMoment B raw54step1 raw54step1Labels := by
      have ha : raw54step1 = raw54step0 := by apply Matrix.ext; unfold raw54step1 raw54step0; decide +kernel
      have hl : raw54step0Labels = labelEmbedding1 ∘ raw54step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw54step0 raw54step0Labels raw54step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1266 node1266Labels := by rfl

def raw55 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw55Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw55step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw55step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical55 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw55 raw55Labels = mixedMoment B node144 node144Labels := by
  calc
    mixedMoment B raw55 raw55Labels = mixedMoment B raw55step0 raw55step0Labels := by
      have ha : raw55step0 = (fun i j => raw55 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw55step0 raw55; decide +kernel
      have hl : raw55step0Labels = raw55Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw55 raw55Labels permutation32 permutation4
    _ = mixedMoment B node144 node144Labels := by rfl

def raw56 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw56Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw56step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw56step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw56step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw56step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical56 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw56 raw56Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw56 raw56Labels = mixedMoment B raw56step0 raw56step0Labels := by
      have ha : raw56step0 = (fun i j => raw56 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw56step0 raw56; decide +kernel
      have hl : raw56step0Labels = raw56Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw56 raw56Labels permutation32 permutation5
    mixedMoment B raw56step0 raw56step0Labels = mixedMoment B raw56step1 raw56step1Labels := by
      have ha : raw56step1 = raw56step0 := by apply Matrix.ext; unfold raw56step1 raw56step0; decide +kernel
      have hl : raw56step0Labels = labelEmbedding1 ∘ raw56step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw56step0 raw56step0Labels raw56step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw57 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw57Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw57step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw57step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical57 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw57 raw57Labels = mixedMoment B node142 node142Labels := by
  calc
    mixedMoment B raw57 raw57Labels = mixedMoment B raw57step0 raw57step0Labels := by
      have ha : raw57step0 = (fun i j => raw57 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw57step0 raw57; decide +kernel
      have hl : raw57step0Labels = raw57Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw57 raw57Labels permutation34 permutation4
    _ = mixedMoment B node142 node142Labels := by rfl

def raw58 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw58Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw58step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw58step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw58step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw58step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical58 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw58 raw58Labels = mixedMoment B node1269 node1269Labels := by
  calc
    mixedMoment B raw58 raw58Labels = mixedMoment B raw58step0 raw58step0Labels := by
      have ha : raw58step0 = (fun i j => raw58 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw58step0 raw58; decide +kernel
      have hl : raw58step0Labels = raw58Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw58 raw58Labels permutation8 permutation5
    mixedMoment B raw58step0 raw58step0Labels = mixedMoment B raw58step1 raw58step1Labels := by
      have ha : raw58step1 = raw58step0 := by apply Matrix.ext; unfold raw58step1 raw58step0; decide +kernel
      have hl : raw58step0Labels = labelEmbedding1 ∘ raw58step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw58step0 raw58step0Labels raw58step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1269 node1269Labels := by rfl

def raw59 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw59Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw59step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw59step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical59 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw59 raw59Labels = mixedMoment B node146 node146Labels := by
  calc
    mixedMoment B raw59 raw59Labels = mixedMoment B raw59step0 raw59step0Labels := by
      have ha : raw59step0 = (fun i j => raw59 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw59step0 raw59; decide +kernel
      have hl : raw59step0Labels = raw59Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw59 raw59Labels permutation8 permutation4
    _ = mixedMoment B node146 node146Labels := by rfl

def raw60 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw60Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw60step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw60step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw60step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw60step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical60 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw60 raw60Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw60 raw60Labels = mixedMoment B raw60step0 raw60step0Labels := by
      have ha : raw60step0 = (fun i j => raw60 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw60step0 raw60; decide +kernel
      have hl : raw60step0Labels = raw60Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw60 raw60Labels permutation8 permutation5
    mixedMoment B raw60step0 raw60step0Labels = mixedMoment B raw60step1 raw60step1Labels := by
      have ha : raw60step1 = raw60step0 := by apply Matrix.ext; unfold raw60step1 raw60step0; decide +kernel
      have hl : raw60step0Labels = labelEmbedding1 ∘ raw60step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw60step0 raw60step0Labels raw60step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1271 node1271Labels := by rfl

def raw61 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw61Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw61step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw61step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical61 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw61 raw61Labels = mixedMoment B node143 node143Labels := by
  calc
    mixedMoment B raw61 raw61Labels = mixedMoment B raw61step0 raw61step0Labels := by
      have ha : raw61step0 = (fun i j => raw61 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw61step0 raw61; decide +kernel
      have hl : raw61step0Labels = raw61Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw61 raw61Labels permutation8 permutation4
    _ = mixedMoment B node143 node143Labels := by rfl

def raw62 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw62Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw62step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw62step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw62step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw62step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical62 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw62 raw62Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw62 raw62Labels = mixedMoment B raw62step0 raw62step0Labels := by
      have ha : raw62step0 = (fun i j => raw62 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw62step0 raw62; decide +kernel
      have hl : raw62step0Labels = raw62Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw62 raw62Labels permutation8 permutation5
    mixedMoment B raw62step0 raw62step0Labels = mixedMoment B raw62step1 raw62step1Labels := by
      have ha : raw62step1 = raw62step0 := by apply Matrix.ext; unfold raw62step1 raw62step0; decide +kernel
      have hl : raw62step0Labels = labelEmbedding1 ∘ raw62step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw62step0 raw62step0Labels raw62step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw63 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw63Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw63step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw63step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical63 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw63 raw63Labels = mixedMoment B node149 node149Labels := by
  calc
    mixedMoment B raw63 raw63Labels = mixedMoment B raw63step0 raw63step0Labels := by
      have ha : raw63step0 = (fun i j => raw63 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw63step0 raw63; decide +kernel
      have hl : raw63step0Labels = raw63Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw63 raw63Labels permutation9 permutation4
    _ = mixedMoment B node149 node149Labels := by rfl

def raw64 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 4, -3]]
def raw64Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw64step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw64step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw64step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw64step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical64 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw64 raw64Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw64 raw64Labels = mixedMoment B raw64step0 raw64step0Labels := by
      have ha : raw64step0 = (fun i j => raw64 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw64step0 raw64; decide +kernel
      have hl : raw64step0Labels = raw64Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw64 raw64Labels permutation2 permutation5
    mixedMoment B raw64step0 raw64step0Labels = mixedMoment B raw64step1 raw64step1Labels := by
      have ha : raw64step1 = raw64step0 := by apply Matrix.ext; unfold raw64step1 raw64step0; decide +kernel
      have hl : raw64step0Labels = labelEmbedding1 ∘ raw64step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw64step0 raw64step0Labels raw64step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw65 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 4, -3]]
def raw65Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw65step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw65step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw65step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw65step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical65 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw65 raw65Labels = mixedMoment B node100 node100Labels := by
  calc
    mixedMoment B raw65 raw65Labels = mixedMoment B raw65step0 raw65step0Labels := by
      have ha : raw65step0 = (fun i j => raw65 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw65step0 raw65; decide +kernel
      have hl : raw65step0Labels = raw65Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw65 raw65Labels permutation7 permutation4
    mixedMoment B raw65step0 raw65step0Labels = mixedMoment B raw65step1 raw65step1Labels := by
      have ha : raw65step1 = -raw65step0 := by apply Matrix.ext; change ∀ i j, raw65step1 i j = -(raw65step0 i j); unfold raw65step1 raw65step0; decide +kernel
      have hl : raw65step1Labels = raw65step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node100 node100Labels := by rfl

def raw66 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw66Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw66step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw66step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw66step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw66step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical66 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw66 raw66Labels = mixedMoment B node1281 node1281Labels := by
  calc
    mixedMoment B raw66 raw66Labels = mixedMoment B raw66step0 raw66step0Labels := by
      have ha : raw66step0 = (fun i j => raw66 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw66step0 raw66; decide +kernel
      have hl : raw66step0Labels = raw66Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw66 raw66Labels permutation8 permutation5
    mixedMoment B raw66step0 raw66step0Labels = mixedMoment B raw66step1 raw66step1Labels := by
      have ha : raw66step1 = raw66step0 := by apply Matrix.ext; unfold raw66step1 raw66step0; decide +kernel
      have hl : raw66step0Labels = labelEmbedding1 ∘ raw66step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw66step0 raw66step0Labels raw66step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1281 node1281Labels := by rfl

def raw67 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw67Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw67step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw67step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical67 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw67 raw67Labels = mixedMoment B node135 node135Labels := by
  calc
    mixedMoment B raw67 raw67Labels = mixedMoment B raw67step0 raw67step0Labels := by
      have ha : raw67step0 = (fun i j => raw67 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw67step0 raw67; decide +kernel
      have hl : raw67step0Labels = raw67Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw67 raw67Labels permutation8 permutation4
    _ = mixedMoment B node135 node135Labels := by rfl

def raw68 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw68Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw68step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw68step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw68step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw68step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical68 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw68 raw68Labels = mixedMoment B node1284 node1284Labels := by
  calc
    mixedMoment B raw68 raw68Labels = mixedMoment B raw68step0 raw68step0Labels := by
      have ha : raw68step0 = (fun i j => raw68 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw68step0 raw68; decide +kernel
      have hl : raw68step0Labels = raw68Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw68 raw68Labels permutation8 permutation5
    mixedMoment B raw68step0 raw68step0Labels = mixedMoment B raw68step1 raw68step1Labels := by
      have ha : raw68step1 = raw68step0 := by apply Matrix.ext; unfold raw68step1 raw68step0; decide +kernel
      have hl : raw68step0Labels = labelEmbedding1 ∘ raw68step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw68step0 raw68step0Labels raw68step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1284 node1284Labels := by rfl

def raw69 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw69Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw69step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw69step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical69 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw69 raw69Labels = mixedMoment B node136 node136Labels := by
  calc
    mixedMoment B raw69 raw69Labels = mixedMoment B raw69step0 raw69step0Labels := by
      have ha : raw69step0 = (fun i j => raw69 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw69step0 raw69; decide +kernel
      have hl : raw69step0Labels = raw69Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw69 raw69Labels permutation8 permutation4
    _ = mixedMoment B node136 node136Labels := by rfl

def raw70 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 4, -4]]
def raw70Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw70step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def raw70step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw70step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def raw70step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical70 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw70 raw70Labels = mixedMoment B node1285 node1285Labels := by
  calc
    mixedMoment B raw70 raw70Labels = mixedMoment B raw70step0 raw70step0Labels := by
      have ha : raw70step0 = (fun i j => raw70 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw70step0 raw70; decide +kernel
      have hl : raw70step0Labels = raw70Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw70 raw70Labels permutation2 permutation5
    mixedMoment B raw70step0 raw70step0Labels = mixedMoment B raw70step1 raw70step1Labels := by
      have ha : raw70step1 = raw70step0 := by apply Matrix.ext; unfold raw70step1 raw70step0; decide +kernel
      have hl : raw70step0Labels = labelEmbedding1 ∘ raw70step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw70step0 raw70step0Labels raw70step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1285 node1285Labels := by rfl

def raw71 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 4, -4]]
def raw71Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw71step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-4, 2, 2]]
def raw71step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw71step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw71step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical71 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw71 raw71Labels = mixedMoment B node57 node57Labels := by
  calc
    mixedMoment B raw71 raw71Labels = mixedMoment B raw71step0 raw71step0Labels := by
      have ha : raw71step0 = (fun i j => raw71 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw71step0 raw71; decide +kernel
      have hl : raw71step0Labels = raw71Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw71 raw71Labels permutation7 permutation4
    mixedMoment B raw71step0 raw71step0Labels = mixedMoment B raw71step1 raw71step1Labels := by
      have ha : raw71step1 = -raw71step0 := by apply Matrix.ext; change ∀ i j, raw71step1 i j = -(raw71step0 i j); unfold raw71step1 raw71step0; decide +kernel
      have hl : raw71step1Labels = raw71step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node57 node57Labels := by rfl

def raw72 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw72Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw72step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw72step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw72step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw72step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical72 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw72 raw72Labels = mixedMoment B node1298 node1298Labels := by
  calc
    mixedMoment B raw72 raw72Labels = mixedMoment B raw72step0 raw72step0Labels := by
      have ha : raw72step0 = (fun i j => raw72 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw72step0 raw72; decide +kernel
      have hl : raw72step0Labels = raw72Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw72 raw72Labels permutation32 permutation5
    mixedMoment B raw72step0 raw72step0Labels = mixedMoment B raw72step1 raw72step1Labels := by
      have ha : raw72step1 = raw72step0 := by apply Matrix.ext; unfold raw72step1 raw72step0; decide +kernel
      have hl : raw72step0Labels = labelEmbedding1 ∘ raw72step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw72step0 raw72step0Labels raw72step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1298 node1298Labels := by rfl

def raw73 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw73Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw73step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw73step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical73 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw73 raw73Labels = mixedMoment B node151 node151Labels := by
  calc
    mixedMoment B raw73 raw73Labels = mixedMoment B raw73step0 raw73step0Labels := by
      have ha : raw73step0 = (fun i j => raw73 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw73step0 raw73; decide +kernel
      have hl : raw73step0Labels = raw73Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw73 raw73Labels permutation50 permutation4
    _ = mixedMoment B node151 node151Labels := by rfl

def raw74 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw74Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw74step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw74step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw74step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw74step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical74 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw74 raw74Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw74 raw74Labels = mixedMoment B raw74step0 raw74step0Labels := by
      have ha : raw74step0 = (fun i j => raw74 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw74step0 raw74; decide +kernel
      have hl : raw74step0Labels = raw74Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw74 raw74Labels permutation32 permutation5
    mixedMoment B raw74step0 raw74step0Labels = mixedMoment B raw74step1 raw74step1Labels := by
      have ha : raw74step1 = raw74step0 := by apply Matrix.ext; unfold raw74step1 raw74step0; decide +kernel
      have hl : raw74step0Labels = labelEmbedding1 ∘ raw74step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw74step0 raw74step0Labels raw74step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw75 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw75Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw75step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw75step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical75 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw75 raw75Labels = mixedMoment B node155 node155Labels := by
  calc
    mixedMoment B raw75 raw75Labels = mixedMoment B raw75step0 raw75step0Labels := by
      have ha : raw75step0 = (fun i j => raw75 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw75step0 raw75; decide +kernel
      have hl : raw75step0Labels = raw75Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw75 raw75Labels permutation48 permutation4
    _ = mixedMoment B node155 node155Labels := by rfl

def raw76 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw76Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw76step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw76step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw76step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw76step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical76 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw76 raw76Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw76 raw76Labels = mixedMoment B raw76step0 raw76step0Labels := by
      have ha : raw76step0 = (fun i j => raw76 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw76step0 raw76; decide +kernel
      have hl : raw76step0Labels = raw76Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw76 raw76Labels permutation8 permutation5
    mixedMoment B raw76step0 raw76step0Labels = mixedMoment B raw76step1 raw76step1Labels := by
      have ha : raw76step1 = raw76step0 := by apply Matrix.ext; unfold raw76step1 raw76step0; decide +kernel
      have hl : raw76step0Labels = labelEmbedding1 ∘ raw76step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw76step0 raw76step0Labels raw76step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1300 node1300Labels := by rfl

def raw77 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw77Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw77step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw77step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical77 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw77 raw77Labels = mixedMoment B node156 node156Labels := by
  calc
    mixedMoment B raw77 raw77Labels = mixedMoment B raw77step0 raw77step0Labels := by
      have ha : raw77step0 = (fun i j => raw77 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw77step0 raw77; decide +kernel
      have hl : raw77step0Labels = raw77Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw77 raw77Labels permutation8 permutation5
    _ = mixedMoment B node156 node156Labels := by rfl

def raw78 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw78Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw78step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw78step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw78step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw78step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical78 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw78 raw78Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw78 raw78Labels = mixedMoment B raw78step0 raw78step0Labels := by
      have ha : raw78step0 = (fun i j => raw78 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw78step0 raw78; decide +kernel
      have hl : raw78step0Labels = raw78Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw78 raw78Labels permutation8 permutation5
    mixedMoment B raw78step0 raw78step0Labels = mixedMoment B raw78step1 raw78step1Labels := by
      have ha : raw78step1 = raw78step0 := by apply Matrix.ext; unfold raw78step1 raw78step0; decide +kernel
      have hl : raw78step0Labels = labelEmbedding1 ∘ raw78step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw78step0 raw78step0Labels raw78step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw79 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw79Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw79step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw79step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical79 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw79 raw79Labels = mixedMoment B node157 node157Labels := by
  calc
    mixedMoment B raw79 raw79Labels = mixedMoment B raw79step0 raw79step0Labels := by
      have ha : raw79step0 = (fun i j => raw79 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw79step0 raw79; decide +kernel
      have hl : raw79step0Labels = raw79Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw79 raw79Labels permutation10 permutation4
    _ = mixedMoment B node157 node157Labels := by rfl

def raw80 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw80Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw80step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw80step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw80step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw80step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical80 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw80 raw80Labels = mixedMoment B node1302 node1302Labels := by
  calc
    mixedMoment B raw80 raw80Labels = mixedMoment B raw80step0 raw80step0Labels := by
      have ha : raw80step0 = (fun i j => raw80 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw80step0 raw80; decide +kernel
      have hl : raw80step0Labels = raw80Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw80 raw80Labels permutation8 permutation5
    mixedMoment B raw80step0 raw80step0Labels = mixedMoment B raw80step1 raw80step1Labels := by
      have ha : raw80step1 = raw80step0 := by apply Matrix.ext; unfold raw80step1 raw80step0; decide +kernel
      have hl : raw80step0Labels = labelEmbedding1 ∘ raw80step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw80step0 raw80step0Labels raw80step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1302 node1302Labels := by rfl

def raw81 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw81Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw81step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw81step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical81 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw81 raw81Labels = mixedMoment B node152 node152Labels := by
  calc
    mixedMoment B raw81 raw81Labels = mixedMoment B raw81step0 raw81step0Labels := by
      have ha : raw81step0 = (fun i j => raw81 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw81step0 raw81; decide +kernel
      have hl : raw81step0Labels = raw81Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw81 raw81Labels permutation10 permutation4
    _ = mixedMoment B node152 node152Labels := by rfl

def raw82 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-2, 3, -1]]
def raw82Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw82step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw82step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw82step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw82step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical82 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw82 raw82Labels = mixedMoment B node1304 node1304Labels := by
  calc
    mixedMoment B raw82 raw82Labels = mixedMoment B raw82step0 raw82step0Labels := by
      have ha : raw82step0 = (fun i j => raw82 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw82step0 raw82; decide +kernel
      have hl : raw82step0Labels = raw82Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw82 raw82Labels permutation2 permutation5
    mixedMoment B raw82step0 raw82step0Labels = mixedMoment B raw82step1 raw82step1Labels := by
      have ha : raw82step1 = raw82step0 := by apply Matrix.ext; unfold raw82step1 raw82step0; decide +kernel
      have hl : raw82step0Labels = labelEmbedding1 ∘ raw82step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw82step0 raw82step0Labels raw82step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1304 node1304Labels := by rfl

def raw83 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-2, 3, -1]]
def raw83Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw83step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw83step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical83 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw83 raw83Labels = mixedMoment B node158 node158Labels := by
  calc
    mixedMoment B raw83 raw83Labels = mixedMoment B raw83step0 raw83step0Labels := by
      have ha : raw83step0 = (fun i j => raw83 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw83step0 raw83; decide +kernel
      have hl : raw83step0Labels = raw83Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw83 raw83Labels permutation2 permutation5
    _ = mixedMoment B node158 node158Labels := by rfl

def raw84 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw84Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw84step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw84step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw84step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw84step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical84 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw84 raw84Labels = mixedMoment B node1305 node1305Labels := by
  calc
    mixedMoment B raw84 raw84Labels = mixedMoment B raw84step0 raw84step0Labels := by
      have ha : raw84step0 = (fun i j => raw84 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw84step0 raw84; decide +kernel
      have hl : raw84step0Labels = raw84Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw84 raw84Labels permutation8 permutation5
    mixedMoment B raw84step0 raw84step0Labels = mixedMoment B raw84step1 raw84step1Labels := by
      have ha : raw84step1 = raw84step0 := by apply Matrix.ext; unfold raw84step1 raw84step0; decide +kernel
      have hl : raw84step0Labels = labelEmbedding1 ∘ raw84step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw84step0 raw84step0Labels raw84step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1305 node1305Labels := by rfl

def raw85 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw85Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw85step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw85step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical85 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw85 raw85Labels = mixedMoment B node156 node156Labels := by
  calc
    mixedMoment B raw85 raw85Labels = mixedMoment B raw85step0 raw85step0Labels := by
      have ha : raw85step0 = (fun i j => raw85 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw85step0 raw85; decide +kernel
      have hl : raw85step0Labels = raw85Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw85 raw85Labels permutation8 permutation4
    _ = mixedMoment B node156 node156Labels := by rfl

def raw86 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 3, -2]]
def raw86Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw86step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw86step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw86step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw86step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical86 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw86 raw86Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw86 raw86Labels = mixedMoment B raw86step0 raw86step0Labels := by
      have ha : raw86step0 = (fun i j => raw86 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw86step0 raw86; decide +kernel
      have hl : raw86step0Labels = raw86Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw86 raw86Labels permutation2 permutation5
    mixedMoment B raw86step0 raw86step0Labels = mixedMoment B raw86step1 raw86step1Labels := by
      have ha : raw86step1 = raw86step0 := by apply Matrix.ext; unfold raw86step1 raw86step0; decide +kernel
      have hl : raw86step0Labels = labelEmbedding1 ∘ raw86step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw86step0 raw86step0Labels raw86step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1307 node1307Labels := by rfl

def raw87 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 3, -2]]
def raw87Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw87step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw87step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical87 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw87 raw87Labels = mixedMoment B node158 node158Labels := by
  calc
    mixedMoment B raw87 raw87Labels = mixedMoment B raw87step0 raw87step0Labels := by
      have ha : raw87step0 = (fun i j => raw87 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw87step0 raw87; decide +kernel
      have hl : raw87step0Labels = raw87Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw87 raw87Labels permutation2 permutation4
    _ = mixedMoment B node158 node158Labels := by rfl

def raw88 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 3, -3]]
def raw88Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw88step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw88step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw88step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw88step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical88 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw88 raw88Labels = mixedMoment B node1308 node1308Labels := by
  calc
    mixedMoment B raw88 raw88Labels = mixedMoment B raw88step0 raw88step0Labels := by
      have ha : raw88step0 = (fun i j => raw88 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw88step0 raw88; decide +kernel
      have hl : raw88step0Labels = raw88Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw88 raw88Labels permutation2 permutation5
    mixedMoment B raw88step0 raw88step0Labels = mixedMoment B raw88step1 raw88step1Labels := by
      have ha : raw88step1 = raw88step0 := by apply Matrix.ext; unfold raw88step1 raw88step0; decide +kernel
      have hl : raw88step0Labels = labelEmbedding1 ∘ raw88step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw88step0 raw88step0Labels raw88step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1308 node1308Labels := by rfl

def raw89 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 3, -3]]
def raw89Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw89step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw89step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical89 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw89 raw89Labels = mixedMoment B node154 node154Labels := by
  calc
    mixedMoment B raw89 raw89Labels = mixedMoment B raw89step0 raw89step0Labels := by
      have ha : raw89step0 = (fun i j => raw89 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw89step0 raw89; decide +kernel
      have hl : raw89step0Labels = raw89Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw89 raw89Labels permutation2 permutation4
    _ = mixedMoment B node154 node154Labels := by rfl

def raw90 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![0, 2, -2], ![-2, 2, 0]]
def raw90Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw90step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw90step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw90step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw90step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical90 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw90 raw90Labels = mixedMoment B node1311 node1311Labels := by
  calc
    mixedMoment B raw90 raw90Labels = mixedMoment B raw90step0 raw90step0Labels := by
      have ha : raw90step0 = (fun i j => raw90 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw90step0 raw90; decide +kernel
      have hl : raw90step0Labels = raw90Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw90 raw90Labels permutation2 permutation5
    mixedMoment B raw90step0 raw90step0Labels = mixedMoment B raw90step1 raw90step1Labels := by
      have ha : raw90step1 = raw90step0 := by apply Matrix.ext; unfold raw90step1 raw90step0; decide +kernel
      have hl : raw90step0Labels = labelEmbedding1 ∘ raw90step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw90step0 raw90step0Labels raw90step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1311 node1311Labels := by rfl

def raw91 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![0, 2, -2], ![-2, 2, 0]]
def raw91Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw91step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw91step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical91 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw91 raw91Labels = mixedMoment B node160 node160Labels := by
  calc
    mixedMoment B raw91 raw91Labels = mixedMoment B raw91step0 raw91step0Labels := by
      have ha : raw91step0 = (fun i j => raw91 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw91step0 raw91; decide +kernel
      have hl : raw91step0Labels = raw91Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw91 raw91Labels permutation3 permutation4
    _ = mixedMoment B node160 node160Labels := by rfl

def raw92 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw92Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw92step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw92step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw92step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw92step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical92 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw92 raw92Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw92 raw92Labels = mixedMoment B raw92step0 raw92step0Labels := by
      have ha : raw92step0 = (fun i j => raw92 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw92step0 raw92; decide +kernel
      have hl : raw92step0Labels = raw92Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw92 raw92Labels permutation2 permutation5
    mixedMoment B raw92step0 raw92step0Labels = mixedMoment B raw92step1 raw92step1Labels := by
      have ha : raw92step1 = raw92step0 := by apply Matrix.ext; unfold raw92step1 raw92step0; decide +kernel
      have hl : raw92step0Labels = labelEmbedding1 ∘ raw92step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw92step0 raw92step0Labels raw92step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1312 node1312Labels := by rfl

def raw93 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw93Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw93step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw93step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical93 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw93 raw93Labels = mixedMoment B node161 node161Labels := by
  calc
    mixedMoment B raw93 raw93Labels = mixedMoment B raw93step0 raw93step0Labels := by
      have ha : raw93step0 = (fun i j => raw93 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw93step0 raw93; decide +kernel
      have hl : raw93step0Labels = raw93Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw93 raw93Labels permutation2 permutation4
    _ = mixedMoment B node161 node161Labels := by rfl

def raw94 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 4, -2]]
def raw94Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw94step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw94step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw94step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw94step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical94 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw94 raw94Labels = mixedMoment B node1313 node1313Labels := by
  calc
    mixedMoment B raw94 raw94Labels = mixedMoment B raw94step0 raw94step0Labels := by
      have ha : raw94step0 = (fun i j => raw94 (permutation0 i) (permutation5 j)) := by apply Matrix.ext; unfold raw94step0 raw94; decide +kernel
      have hl : raw94step0Labels = raw94Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw94 raw94Labels permutation0 permutation5
    mixedMoment B raw94step0 raw94step0Labels = mixedMoment B raw94step1 raw94step1Labels := by
      have ha : raw94step1 = raw94step0 := by apply Matrix.ext; unfold raw94step1 raw94step0; decide +kernel
      have hl : raw94step0Labels = labelEmbedding1 ∘ raw94step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw94step0 raw94step0Labels raw94step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1313 node1313Labels := by rfl

def raw95 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 4, -2]]
def raw95Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw95step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw95step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical95 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw95 raw95Labels = mixedMoment B node162 node162Labels := by
  calc
    mixedMoment B raw95 raw95Labels = mixedMoment B raw95step0 raw95step0Labels := by
      have ha : raw95step0 = (fun i j => raw95 (permutation0 i) (permutation4 j)) := by apply Matrix.ext; unfold raw95step0 raw95; decide +kernel
      have hl : raw95step0Labels = raw95Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw95 raw95Labels permutation0 permutation4
    _ = mixedMoment B node162 node162Labels := by rfl

def raw96 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw96Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw96step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw96step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw96step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw96step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical96 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw96 raw96Labels = mixedMoment B node1339 node1339Labels := by
  calc
    mixedMoment B raw96 raw96Labels = mixedMoment B raw96step0 raw96step0Labels := by
      have ha : raw96step0 = (fun i j => raw96 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw96step0 raw96; decide +kernel
      have hl : raw96step0Labels = raw96Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw96 raw96Labels permutation152 permutation5
    mixedMoment B raw96step0 raw96step0Labels = mixedMoment B raw96step1 raw96step1Labels := by
      have ha : raw96step1 = raw96step0 := by apply Matrix.ext; unfold raw96step1 raw96step0; decide +kernel
      have hl : raw96step0Labels = labelEmbedding1 ∘ raw96step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw96step0 raw96step0Labels raw96step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1339 node1339Labels := by rfl

def raw97 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw97Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw97step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw97step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical97 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw97 raw97Labels = mixedMoment B node63 node63Labels := by
  calc
    mixedMoment B raw97 raw97Labels = mixedMoment B raw97step0 raw97step0Labels := by
      have ha : raw97step0 = (fun i j => raw97 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw97step0 raw97; decide +kernel
      have hl : raw97step0Labels = raw97Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw97 raw97Labels permutation164 permutation4
    _ = mixedMoment B node63 node63Labels := by rfl

def raw98 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw98Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw98step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw98step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw98step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw98step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical98 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw98 raw98Labels = mixedMoment B node1340 node1340Labels := by
  calc
    mixedMoment B raw98 raw98Labels = mixedMoment B raw98step0 raw98step0Labels := by
      have ha : raw98step0 = (fun i j => raw98 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw98step0 raw98; decide +kernel
      have hl : raw98step0Labels = raw98Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw98 raw98Labels permutation32 permutation5
    mixedMoment B raw98step0 raw98step0Labels = mixedMoment B raw98step1 raw98step1Labels := by
      have ha : raw98step1 = raw98step0 := by apply Matrix.ext; unfold raw98step1 raw98step0; decide +kernel
      have hl : raw98step0Labels = labelEmbedding1 ∘ raw98step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw98step0 raw98step0Labels raw98step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1340 node1340Labels := by rfl

def raw99 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw99Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw99step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw99step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical99 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw99 raw99Labels = mixedMoment B node66 node66Labels := by
  calc
    mixedMoment B raw99 raw99Labels = mixedMoment B raw99step0 raw99step0Labels := by
      have ha : raw99step0 = (fun i j => raw99 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw99step0 raw99; decide +kernel
      have hl : raw99step0Labels = raw99Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw99 raw99Labels permutation32 permutation4
    _ = mixedMoment B node66 node66Labels := by rfl

def raw100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw100step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw100 raw100Labels = mixedMoment B node1341 node1341Labels := by
  calc
    mixedMoment B raw100 raw100Labels = mixedMoment B raw100step0 raw100step0Labels := by
      have ha : raw100step0 = (fun i j => raw100 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw100step0 raw100; decide +kernel
      have hl : raw100step0Labels = raw100Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw100 raw100Labels permutation152 permutation5
    mixedMoment B raw100step0 raw100step0Labels = mixedMoment B raw100step1 raw100step1Labels := by
      have ha : raw100step1 = raw100step0 := by apply Matrix.ext; unfold raw100step1 raw100step0; decide +kernel
      have hl : raw100step0Labels = labelEmbedding1 ∘ raw100step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw100step0 raw100step0Labels raw100step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1341 node1341Labels := by rfl

def raw101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw101Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw101step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw101 raw101Labels = mixedMoment B node61 node61Labels := by
  calc
    mixedMoment B raw101 raw101Labels = mixedMoment B raw101step0 raw101step0Labels := by
      have ha : raw101step0 = (fun i j => raw101 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw101step0 raw101; decide +kernel
      have hl : raw101step0Labels = raw101Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw101 raw101Labels permutation160 permutation4
    _ = mixedMoment B node61 node61Labels := by rfl

def raw102 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw102 raw102Labels = mixedMoment B node1342 node1342Labels := by
  calc
    mixedMoment B raw102 raw102Labels = mixedMoment B raw102step0 raw102step0Labels := by
      have ha : raw102step0 = (fun i j => raw102 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw102step0 raw102; decide +kernel
      have hl : raw102step0Labels = raw102Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw102 raw102Labels permutation32 permutation5
    mixedMoment B raw102step0 raw102step0Labels = mixedMoment B raw102step1 raw102step1Labels := by
      have ha : raw102step1 = raw102step0 := by apply Matrix.ext; unfold raw102step1 raw102step0; decide +kernel
      have hl : raw102step0Labels = labelEmbedding1 ∘ raw102step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw102step0 raw102step0Labels raw102step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1342 node1342Labels := by rfl

def raw103 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw103Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw103step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw103 raw103Labels = mixedMoment B node64 node64Labels := by
  calc
    mixedMoment B raw103 raw103Labels = mixedMoment B raw103step0 raw103step0Labels := by
      have ha : raw103step0 = (fun i j => raw103 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw103step0 raw103; decide +kernel
      have hl : raw103step0Labels = raw103Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw103 raw103Labels permutation34 permutation4
    _ = mixedMoment B node64 node64Labels := by rfl

def raw104 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw104step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw104 raw104Labels = mixedMoment B node1343 node1343Labels := by
  calc
    mixedMoment B raw104 raw104Labels = mixedMoment B raw104step0 raw104step0Labels := by
      have ha : raw104step0 = (fun i j => raw104 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw104step0 raw104; decide +kernel
      have hl : raw104step0Labels = raw104Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw104 raw104Labels permutation32 permutation5
    mixedMoment B raw104step0 raw104step0Labels = mixedMoment B raw104step1 raw104step1Labels := by
      have ha : raw104step1 = raw104step0 := by apply Matrix.ext; unfold raw104step1 raw104step0; decide +kernel
      have hl : raw104step0Labels = labelEmbedding1 ∘ raw104step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw104step0 raw104step0Labels raw104step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1343 node1343Labels := by rfl

def raw105 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw105Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw105step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw105 raw105Labels = mixedMoment B node68 node68Labels := by
  calc
    mixedMoment B raw105 raw105Labels = mixedMoment B raw105step0 raw105step0Labels := by
      have ha : raw105step0 = (fun i j => raw105 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw105step0 raw105; decide +kernel
      have hl : raw105step0Labels = raw105Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw105 raw105Labels permutation33 permutation4
    _ = mixedMoment B node68 node68Labels := by rfl

def raw106 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw106step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw106 raw106Labels = mixedMoment B node1344 node1344Labels := by
  calc
    mixedMoment B raw106 raw106Labels = mixedMoment B raw106step0 raw106step0Labels := by
      have ha : raw106step0 = (fun i j => raw106 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw106step0 raw106; decide +kernel
      have hl : raw106step0Labels = raw106Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw106 raw106Labels permutation32 permutation5
    mixedMoment B raw106step0 raw106step0Labels = mixedMoment B raw106step1 raw106step1Labels := by
      have ha : raw106step1 = raw106step0 := by apply Matrix.ext; unfold raw106step1 raw106step0; decide +kernel
      have hl : raw106step0Labels = labelEmbedding1 ∘ raw106step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw106step0 raw106step0Labels raw106step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1344 node1344Labels := by rfl

def raw107 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw107Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw107step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw107 raw107Labels = mixedMoment B node69 node69Labels := by
  calc
    mixedMoment B raw107 raw107Labels = mixedMoment B raw107step0 raw107step0Labels := by
      have ha : raw107step0 = (fun i j => raw107 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw107step0 raw107; decide +kernel
      have hl : raw107step0Labels = raw107Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw107 raw107Labels permutation32 permutation4
    _ = mixedMoment B node69 node69Labels := by rfl

def raw108 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw108step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw108 raw108Labels = mixedMoment B node1346 node1346Labels := by
  calc
    mixedMoment B raw108 raw108Labels = mixedMoment B raw108step0 raw108step0Labels := by
      have ha : raw108step0 = (fun i j => raw108 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw108step0 raw108; decide +kernel
      have hl : raw108step0Labels = raw108Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw108 raw108Labels permutation32 permutation5
    mixedMoment B raw108step0 raw108step0Labels = mixedMoment B raw108step1 raw108step1Labels := by
      have ha : raw108step1 = raw108step0 := by apply Matrix.ext; unfold raw108step1 raw108step0; decide +kernel
      have hl : raw108step0Labels = labelEmbedding1 ∘ raw108step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw108step0 raw108step0Labels raw108step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1346 node1346Labels := by rfl

def raw109 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw109Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw109step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw109 raw109Labels = mixedMoment B node62 node62Labels := by
  calc
    mixedMoment B raw109 raw109Labels = mixedMoment B raw109step0 raw109step0Labels := by
      have ha : raw109step0 = (fun i j => raw109 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw109step0 raw109; decide +kernel
      have hl : raw109step0Labels = raw109Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw109 raw109Labels permutation32 permutation4
    _ = mixedMoment B node62 node62Labels := by rfl

def raw110 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw110step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw110 raw110Labels = mixedMoment B node1349 node1349Labels := by
  calc
    mixedMoment B raw110 raw110Labels = mixedMoment B raw110step0 raw110step0Labels := by
      have ha : raw110step0 = (fun i j => raw110 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw110step0 raw110; decide +kernel
      have hl : raw110step0Labels = raw110Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw110 raw110Labels permutation8 permutation5
    mixedMoment B raw110step0 raw110step0Labels = mixedMoment B raw110step1 raw110step1Labels := by
      have ha : raw110step1 = raw110step0 := by apply Matrix.ext; unfold raw110step1 raw110step0; decide +kernel
      have hl : raw110step0Labels = labelEmbedding1 ∘ raw110step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw110step0 raw110step0Labels raw110step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1349 node1349Labels := by rfl

def raw111 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw111Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw111step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw111step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw111 raw111Labels = mixedMoment B node71 node71Labels := by
  calc
    mixedMoment B raw111 raw111Labels = mixedMoment B raw111step0 raw111step0Labels := by
      have ha : raw111step0 = (fun i j => raw111 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw111step0 raw111; decide +kernel
      have hl : raw111step0Labels = raw111Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw111 raw111Labels permutation8 permutation4
    _ = mixedMoment B node71 node71Labels := by rfl

def raw112 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw112 raw112Labels = mixedMoment B node1395 node1395Labels := by
  calc
    mixedMoment B raw112 raw112Labels = mixedMoment B raw112step0 raw112step0Labels := by
      have ha : raw112step0 = (fun i j => raw112 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw112step0 raw112; decide +kernel
      have hl : raw112step0Labels = raw112Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw112 raw112Labels permutation152 permutation5
    mixedMoment B raw112step0 raw112step0Labels = mixedMoment B raw112step1 raw112step1Labels := by
      have ha : raw112step1 = raw112step0 := by apply Matrix.ext; unfold raw112step1 raw112step0; decide +kernel
      have hl : raw112step0Labels = labelEmbedding1 ∘ raw112step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw112step0 raw112step0Labels raw112step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1395 node1395Labels := by rfl

def raw113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw113Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw113step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw113 raw113Labels = mixedMoment B node79 node79Labels := by
  calc
    mixedMoment B raw113 raw113Labels = mixedMoment B raw113step0 raw113step0Labels := by
      have ha : raw113step0 = (fun i j => raw113 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw113step0 raw113; decide +kernel
      have hl : raw113step0Labels = raw113Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw113 raw113Labels permutation176 permutation4
    _ = mixedMoment B node79 node79Labels := by rfl

def raw114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw114 raw114Labels = mixedMoment B node1396 node1396Labels := by
  calc
    mixedMoment B raw114 raw114Labels = mixedMoment B raw114step0 raw114step0Labels := by
      have ha : raw114step0 = (fun i j => raw114 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw114step0 raw114; decide +kernel
      have hl : raw114step0Labels = raw114Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw114 raw114Labels permutation152 permutation5
    mixedMoment B raw114step0 raw114step0Labels = mixedMoment B raw114step1 raw114step1Labels := by
      have ha : raw114step1 = raw114step0 := by apply Matrix.ext; unfold raw114step1 raw114step0; decide +kernel
      have hl : raw114step0Labels = labelEmbedding1 ∘ raw114step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw114step0 raw114step0Labels raw114step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1396 node1396Labels := by rfl

def raw115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw115Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw115step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw115 raw115Labels = mixedMoment B node77 node77Labels := by
  calc
    mixedMoment B raw115 raw115Labels = mixedMoment B raw115step0 raw115step0Labels := by
      have ha : raw115step0 = (fun i j => raw115 (permutation178 i) (permutation4 j)) := by apply Matrix.ext; unfold raw115step0 raw115; decide +kernel
      have hl : raw115step0Labels = raw115Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw115 raw115Labels permutation178 permutation4
    _ = mixedMoment B node77 node77Labels := by rfl

def raw116 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw116step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw116 raw116Labels = mixedMoment B node1397 node1397Labels := by
  calc
    mixedMoment B raw116 raw116Labels = mixedMoment B raw116step0 raw116step0Labels := by
      have ha : raw116step0 = (fun i j => raw116 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw116step0 raw116; decide +kernel
      have hl : raw116step0Labels = raw116Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw116 raw116Labels permutation32 permutation5
    mixedMoment B raw116step0 raw116step0Labels = mixedMoment B raw116step1 raw116step1Labels := by
      have ha : raw116step1 = raw116step0 := by apply Matrix.ext; unfold raw116step1 raw116step0; decide +kernel
      have hl : raw116step0Labels = labelEmbedding1 ∘ raw116step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw116step0 raw116step0Labels raw116step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1397 node1397Labels := by rfl

def raw117 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw117Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw117step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw117 raw117Labels = mixedMoment B node80 node80Labels := by
  calc
    mixedMoment B raw117 raw117Labels = mixedMoment B raw117step0 raw117step0Labels := by
      have ha : raw117step0 = (fun i j => raw117 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw117step0 raw117; decide +kernel
      have hl : raw117step0Labels = raw117Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw117 raw117Labels permutation38 permutation4
    _ = mixedMoment B node80 node80Labels := by rfl

def raw118 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw118step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw118 raw118Labels = mixedMoment B node1399 node1399Labels := by
  calc
    mixedMoment B raw118 raw118Labels = mixedMoment B raw118step0 raw118step0Labels := by
      have ha : raw118step0 = (fun i j => raw118 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw118step0 raw118; decide +kernel
      have hl : raw118step0Labels = raw118Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw118 raw118Labels permutation32 permutation5
    mixedMoment B raw118step0 raw118step0Labels = mixedMoment B raw118step1 raw118step1Labels := by
      have ha : raw118step1 = raw118step0 := by apply Matrix.ext; unfold raw118step1 raw118step0; decide +kernel
      have hl : raw118step0Labels = labelEmbedding1 ∘ raw118step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw118step0 raw118step0Labels raw118step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1399 node1399Labels := by rfl

def raw119 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw119Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw119step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw119 raw119Labels = mixedMoment B node78 node78Labels := by
  calc
    mixedMoment B raw119 raw119Labels = mixedMoment B raw119step0 raw119step0Labels := by
      have ha : raw119step0 = (fun i j => raw119 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw119step0 raw119; decide +kernel
      have hl : raw119step0Labels = raw119Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw119 raw119Labels permutation38 permutation4
    _ = mixedMoment B node78 node78Labels := by rfl

def raw120 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw120step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw120 raw120Labels = mixedMoment B node1401 node1401Labels := by
  calc
    mixedMoment B raw120 raw120Labels = mixedMoment B raw120step0 raw120step0Labels := by
      have ha : raw120step0 = (fun i j => raw120 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw120step0 raw120; decide +kernel
      have hl : raw120step0Labels = raw120Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw120 raw120Labels permutation32 permutation5
    mixedMoment B raw120step0 raw120step0Labels = mixedMoment B raw120step1 raw120step1Labels := by
      have ha : raw120step1 = raw120step0 := by apply Matrix.ext; unfold raw120step1 raw120step0; decide +kernel
      have hl : raw120step0Labels = labelEmbedding1 ∘ raw120step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw120step0 raw120step0Labels raw120step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1401 node1401Labels := by rfl

def raw121 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw121Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw121step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw121 raw121Labels = mixedMoment B node81 node81Labels := by
  calc
    mixedMoment B raw121 raw121Labels = mixedMoment B raw121step0 raw121step0Labels := by
      have ha : raw121step0 = (fun i j => raw121 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw121step0 raw121; decide +kernel
      have hl : raw121step0Labels = raw121Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw121 raw121Labels permutation39 permutation4
    _ = mixedMoment B node81 node81Labels := by rfl

def raw122 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![-1, 4, -3]]
def raw122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw122step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw122step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw122 raw122Labels = mixedMoment B node1402 node1402Labels := by
  calc
    mixedMoment B raw122 raw122Labels = mixedMoment B raw122step0 raw122step0Labels := by
      have ha : raw122step0 = (fun i j => raw122 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw122step0 raw122; decide +kernel
      have hl : raw122step0Labels = raw122Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw122 raw122Labels permutation8 permutation5
    mixedMoment B raw122step0 raw122step0Labels = mixedMoment B raw122step1 raw122step1Labels := by
      have ha : raw122step1 = raw122step0 := by apply Matrix.ext; unfold raw122step1 raw122step0; decide +kernel
      have hl : raw122step0Labels = labelEmbedding1 ∘ raw122step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw122step0 raw122step0Labels raw122step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1402 node1402Labels := by rfl

def raw123 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 0, 1], ![-1, 4, -3]]
def raw123Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw123step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw123step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw123 raw123Labels = mixedMoment B node82 node82Labels := by
  calc
    mixedMoment B raw123 raw123Labels = mixedMoment B raw123step0 raw123step0Labels := by
      have ha : raw123step0 = (fun i j => raw123 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw123step0 raw123; decide +kernel
      have hl : raw123step0Labels = raw123Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw123 raw123Labels permutation10 permutation4
    _ = mixedMoment B node82 node82Labels := by rfl

def raw124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw124step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw124 raw124Labels = mixedMoment B node1409 node1409Labels := by
  calc
    mixedMoment B raw124 raw124Labels = mixedMoment B raw124step0 raw124step0Labels := by
      have ha : raw124step0 = (fun i j => raw124 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw124step0 raw124; decide +kernel
      have hl : raw124step0Labels = raw124Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw124 raw124Labels permutation152 permutation5
    mixedMoment B raw124step0 raw124step0Labels = mixedMoment B raw124step1 raw124step1Labels := by
      have ha : raw124step1 = raw124step0 := by apply Matrix.ext; unfold raw124step1 raw124step0; decide +kernel
      have hl : raw124step0Labels = labelEmbedding1 ∘ raw124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw124step0 raw124step0Labels raw124step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1409 node1409Labels := by rfl

def raw125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw125Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw125step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw125 raw125Labels = mixedMoment B node91 node91Labels := by
  calc
    mixedMoment B raw125 raw125Labels = mixedMoment B raw125step0 raw125step0Labels := by
      have ha : raw125step0 = (fun i j => raw125 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw125step0 raw125; decide +kernel
      have hl : raw125step0Labels = raw125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw125 raw125Labels permutation168 permutation4
    _ = mixedMoment B node91 node91Labels := by rfl

def raw126 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw126step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw126 raw126Labels = mixedMoment B node1410 node1410Labels := by
  calc
    mixedMoment B raw126 raw126Labels = mixedMoment B raw126step0 raw126step0Labels := by
      have ha : raw126step0 = (fun i j => raw126 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw126step0 raw126; decide +kernel
      have hl : raw126step0Labels = raw126Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw126 raw126Labels permutation32 permutation5
    mixedMoment B raw126step0 raw126step0Labels = mixedMoment B raw126step1 raw126step1Labels := by
      have ha : raw126step1 = raw126step0 := by apply Matrix.ext; unfold raw126step1 raw126step0; decide +kernel
      have hl : raw126step0Labels = labelEmbedding1 ∘ raw126step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw126step0 raw126step0Labels raw126step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1410 node1410Labels := by rfl

def raw127 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw127Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw127step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw127 raw127Labels = mixedMoment B node95 node95Labels := by
  calc
    mixedMoment B raw127 raw127Labels = mixedMoment B raw127step0 raw127step0Labels := by
      have ha : raw127step0 = (fun i j => raw127 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw127step0 raw127; decide +kernel
      have hl : raw127step0Labels = raw127Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw127 raw127Labels permutation32 permutation4
    _ = mixedMoment B node95 node95Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
