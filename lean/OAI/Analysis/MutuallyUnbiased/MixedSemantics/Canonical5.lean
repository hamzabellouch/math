import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw640 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw640 raw640Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw640 raw640Labels = mixedMoment B raw640step0 raw640step0Labels := by
      have ha : raw640step0 = (fun i j => raw640 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw640step0 raw640; decide +kernel
      have hl : raw640step0Labels = raw640Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw640 raw640Labels permutation32 permutation5
    mixedMoment B raw640step0 raw640step0Labels = mixedMoment B raw640step1 raw640step1Labels := by
      have ha : raw640step1 = raw640step0 := by apply Matrix.ext; unfold raw640step1 raw640step0; decide +kernel
      have hl : raw640step0Labels = labelEmbedding1 ∘ raw640step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw640step0 raw640step0Labels raw640step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4028 node4028Labels := by rfl

def raw641 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw641Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw641step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw641 raw641Labels = mixedMoment B node500 node500Labels := by
  calc
    mixedMoment B raw641 raw641Labels = mixedMoment B raw641step0 raw641step0Labels := by
      have ha : raw641step0 = (fun i j => raw641 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw641step0 raw641; decide +kernel
      have hl : raw641step0Labels = raw641Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw641 raw641Labels permutation36 permutation4
    _ = mixedMoment B node500 node500Labels := by rfl

def raw642 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw642step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw642 raw642Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw642 raw642Labels = mixedMoment B raw642step0 raw642step0Labels := by
      have ha : raw642step0 = (fun i j => raw642 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw642step0 raw642; decide +kernel
      have hl : raw642step0Labels = raw642Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw642 raw642Labels permutation32 permutation5
    mixedMoment B raw642step0 raw642step0Labels = mixedMoment B raw642step1 raw642step1Labels := by
      have ha : raw642step1 = raw642step0 := by apply Matrix.ext; unfold raw642step1 raw642step0; decide +kernel
      have hl : raw642step0Labels = labelEmbedding1 ∘ raw642step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw642step0 raw642step0Labels raw642step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw643 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw643Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw643step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw643 raw643Labels = mixedMoment B node502 node502Labels := by
  calc
    mixedMoment B raw643 raw643Labels = mixedMoment B raw643step0 raw643step0Labels := by
      have ha : raw643step0 = (fun i j => raw643 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw643step0 raw643; decide +kernel
      have hl : raw643step0Labels = raw643Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw643 raw643Labels permutation35 permutation4
    _ = mixedMoment B node502 node502Labels := by rfl

def raw644 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw644step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw644 raw644Labels = mixedMoment B node4030 node4030Labels := by
  calc
    mixedMoment B raw644 raw644Labels = mixedMoment B raw644step0 raw644step0Labels := by
      have ha : raw644step0 = (fun i j => raw644 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw644step0 raw644; decide +kernel
      have hl : raw644step0Labels = raw644Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw644 raw644Labels permutation8 permutation5
    mixedMoment B raw644step0 raw644step0Labels = mixedMoment B raw644step1 raw644step1Labels := by
      have ha : raw644step1 = raw644step0 := by apply Matrix.ext; unfold raw644step1 raw644step0; decide +kernel
      have hl : raw644step0Labels = labelEmbedding1 ∘ raw644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw644step0 raw644step0Labels raw644step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4030 node4030Labels := by rfl

def raw645 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw645Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw645step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw645step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw645 raw645Labels = mixedMoment B node501 node501Labels := by
  calc
    mixedMoment B raw645 raw645Labels = mixedMoment B raw645step0 raw645step0Labels := by
      have ha : raw645step0 = (fun i j => raw645 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw645step0 raw645; decide +kernel
      have hl : raw645step0Labels = raw645Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw645 raw645Labels permutation8 permutation4
    _ = mixedMoment B node501 node501Labels := by rfl

def raw646 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw646 raw646Labels = mixedMoment B node4031 node4031Labels := by
  calc
    mixedMoment B raw646 raw646Labels = mixedMoment B raw646step0 raw646step0Labels := by
      have ha : raw646step0 = (fun i j => raw646 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw646step0 raw646; decide +kernel
      have hl : raw646step0Labels = raw646Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw646 raw646Labels permutation152 permutation5
    mixedMoment B raw646step0 raw646step0Labels = mixedMoment B raw646step1 raw646step1Labels := by
      have ha : raw646step1 = raw646step0 := by apply Matrix.ext; unfold raw646step1 raw646step0; decide +kernel
      have hl : raw646step0Labels = labelEmbedding1 ∘ raw646step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw646step0 raw646step0Labels raw646step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4031 node4031Labels := by rfl

def raw647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw647Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw647step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw647 raw647Labels = mixedMoment B node471 node471Labels := by
  calc
    mixedMoment B raw647 raw647Labels = mixedMoment B raw647step0 raw647step0Labels := by
      have ha : raw647step0 = (fun i j => raw647 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw647step0 raw647; decide +kernel
      have hl : raw647step0Labels = raw647Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw647 raw647Labels permutation152 permutation4
    _ = mixedMoment B node471 node471Labels := by rfl

def raw648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw648 raw648Labels = mixedMoment B node4032 node4032Labels := by
  calc
    mixedMoment B raw648 raw648Labels = mixedMoment B raw648step0 raw648step0Labels := by
      have ha : raw648step0 = (fun i j => raw648 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw648step0 raw648; decide +kernel
      have hl : raw648step0Labels = raw648Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw648 raw648Labels permutation152 permutation5
    mixedMoment B raw648step0 raw648step0Labels = mixedMoment B raw648step1 raw648step1Labels := by
      have ha : raw648step1 = raw648step0 := by apply Matrix.ext; unfold raw648step1 raw648step0; decide +kernel
      have hl : raw648step0Labels = labelEmbedding1 ∘ raw648step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw648step0 raw648step0Labels raw648step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4032 node4032Labels := by rfl

def raw649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw649Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw649step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw649 raw649Labels = mixedMoment B node478 node478Labels := by
  calc
    mixedMoment B raw649 raw649Labels = mixedMoment B raw649step0 raw649step0Labels := by
      have ha : raw649step0 = (fun i j => raw649 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw649step0 raw649; decide +kernel
      have hl : raw649step0Labels = raw649Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw649 raw649Labels permutation158 permutation4
    _ = mixedMoment B node478 node478Labels := by rfl

def raw650 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw650Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw650step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw650 raw650Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw650 raw650Labels = mixedMoment B raw650step0 raw650step0Labels := by
      have ha : raw650step0 = (fun i j => raw650 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw650step0 raw650; decide +kernel
      have hl : raw650step0Labels = raw650Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw650 raw650Labels permutation152 permutation5
    mixedMoment B raw650step0 raw650step0Labels = mixedMoment B raw650step1 raw650step1Labels := by
      have ha : raw650step1 = raw650step0 := by apply Matrix.ext; unfold raw650step1 raw650step0; decide +kernel
      have hl : raw650step0Labels = labelEmbedding1 ∘ raw650step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw650step0 raw650step0Labels raw650step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw651Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw651step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw651 raw651Labels = mixedMoment B node488 node488Labels := by
  calc
    mixedMoment B raw651 raw651Labels = mixedMoment B raw651step0 raw651step0Labels := by
      have ha : raw651step0 = (fun i j => raw651 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw651step0 raw651; decide +kernel
      have hl : raw651step0Labels = raw651Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw651 raw651Labels permutation155 permutation4
    _ = mixedMoment B node488 node488Labels := by rfl

def raw652 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw652Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw652 raw652Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw652 raw652Labels = mixedMoment B raw652step0 raw652step0Labels := by
      have ha : raw652step0 = (fun i j => raw652 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw652step0 raw652; decide +kernel
      have hl : raw652step0Labels = raw652Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw652 raw652Labels permutation32 permutation5
    mixedMoment B raw652step0 raw652step0Labels = mixedMoment B raw652step1 raw652step1Labels := by
      have ha : raw652step1 = raw652step0 := by apply Matrix.ext; unfold raw652step1 raw652step0; decide +kernel
      have hl : raw652step0Labels = labelEmbedding1 ∘ raw652step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw652step0 raw652step0Labels raw652step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw653 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw653Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw653step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw653 raw653Labels = mixedMoment B node504 node504Labels := by
  calc
    mixedMoment B raw653 raw653Labels = mixedMoment B raw653step0 raw653step0Labels := by
      have ha : raw653step0 = (fun i j => raw653 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw653step0 raw653; decide +kernel
      have hl : raw653step0Labels = raw653Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw653 raw653Labels permutation32 permutation4
    _ = mixedMoment B node504 node504Labels := by rfl

def raw654 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw654Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw654step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw654 raw654Labels = mixedMoment B node4050 node4050Labels := by
  calc
    mixedMoment B raw654 raw654Labels = mixedMoment B raw654step0 raw654step0Labels := by
      have ha : raw654step0 = (fun i j => raw654 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw654step0 raw654; decide +kernel
      have hl : raw654step0Labels = raw654Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw654 raw654Labels permutation32 permutation5
    mixedMoment B raw654step0 raw654step0Labels = mixedMoment B raw654step1 raw654step1Labels := by
      have ha : raw654step1 = raw654step0 := by apply Matrix.ext; unfold raw654step1 raw654step0; decide +kernel
      have hl : raw654step0Labels = labelEmbedding1 ∘ raw654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw654step0 raw654step0Labels raw654step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4050 node4050Labels := by rfl

def raw655 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw655Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw655step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw655step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw655 raw655Labels = mixedMoment B node526 node526Labels := by
  calc
    mixedMoment B raw655 raw655Labels = mixedMoment B raw655step0 raw655step0Labels := by
      have ha : raw655step0 = (fun i j => raw655 (permutation45 i) (permutation2 j)) := by apply Matrix.ext; unfold raw655step0 raw655; decide +kernel
      have hl : raw655step0Labels = raw655Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw655 raw655Labels permutation45 permutation2
    mixedMoment B raw655step0 raw655step0Labels = mixedMoment B raw655step1 raw655step1Labels := by
      have ha : raw655step1 = -raw655step0 := by apply Matrix.ext; change ∀ i j, raw655step1 i j = -(raw655step0 i j); unfold raw655step1 raw655step0; decide +kernel
      have hl : raw655step1Labels = raw655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node526 node526Labels := by rfl

def raw656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1]]
def raw656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw656step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw656 raw656Labels = mixedMoment B node4051 node4051Labels := by
  calc
    mixedMoment B raw656 raw656Labels = mixedMoment B raw656step0 raw656step0Labels := by
      have ha : raw656step0 = (fun i j => raw656 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw656step0 raw656; decide +kernel
      have hl : raw656step0Labels = raw656Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw656 raw656Labels permutation152 permutation5
    mixedMoment B raw656step0 raw656step0Labels = mixedMoment B raw656step1 raw656step1Labels := by
      have ha : raw656step1 = raw656step0 := by apply Matrix.ext; unfold raw656step1 raw656step0; decide +kernel
      have hl : raw656step0Labels = labelEmbedding1 ∘ raw656step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw656step0 raw656step0Labels raw656step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4051 node4051Labels := by rfl

def raw657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1]]
def raw657Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw657step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw657 raw657Labels = mixedMoment B node531 node531Labels := by
  calc
    mixedMoment B raw657 raw657Labels = mixedMoment B raw657step0 raw657step0Labels := by
      have ha : raw657step0 = (fun i j => raw657 (permutation393 i) (permutation2 j)) := by apply Matrix.ext; unfold raw657step0 raw657; decide +kernel
      have hl : raw657step0Labels = raw657Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw657 raw657Labels permutation393 permutation2
    _ = mixedMoment B node531 node531Labels := by rfl

def raw658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw658step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw658 raw658Labels = mixedMoment B node4053 node4053Labels := by
  calc
    mixedMoment B raw658 raw658Labels = mixedMoment B raw658step0 raw658step0Labels := by
      have ha : raw658step0 = (fun i j => raw658 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw658step0 raw658; decide +kernel
      have hl : raw658step0Labels = raw658Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw658 raw658Labels permutation152 permutation5
    mixedMoment B raw658step0 raw658step0Labels = mixedMoment B raw658step1 raw658step1Labels := by
      have ha : raw658step1 = raw658step0 := by apply Matrix.ext; unfold raw658step1 raw658step0; decide +kernel
      have hl : raw658step0Labels = labelEmbedding1 ∘ raw658step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw658step0 raw658step0Labels raw658step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4053 node4053Labels := by rfl

def raw659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw659Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw659step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw659 raw659Labels = mixedMoment B node533 node533Labels := by
  calc
    mixedMoment B raw659 raw659Labels = mixedMoment B raw659step0 raw659step0Labels := by
      have ha : raw659step0 = (fun i j => raw659 (permutation510 i) (permutation2 j)) := by apply Matrix.ext; unfold raw659step0 raw659; decide +kernel
      have hl : raw659step0Labels = raw659Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw659 raw659Labels permutation510 permutation2
    _ = mixedMoment B node533 node533Labels := by rfl

def raw660 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw660Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw660 raw660Labels = mixedMoment B node4093 node4093Labels := by
  calc
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw661 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw661Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw661 raw661Labels = mixedMoment B node5 node5Labels := by
  calc
    _ = mixedMoment B node5 node5Labels := by rfl

def raw662 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw662Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw662 raw662Labels = mixedMoment B node4094 node4094Labels := by
  calc
    _ = mixedMoment B node4094 node4094Labels := by rfl

def raw663 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw663Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw663 raw663Labels = mixedMoment B node6 node6Labels := by
  calc
    _ = mixedMoment B node6 node6Labels := by rfl

def raw664 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw664Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw664 raw664Labels = mixedMoment B node4096 node4096Labels := by
  calc
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw665 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw665Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw665 raw665Labels = mixedMoment B node7 node7Labels := by
  calc
    _ = mixedMoment B node7 node7Labels := by rfl

def raw666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw666step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw666 raw666Labels = mixedMoment B node4098 node4098Labels := by
  calc
    mixedMoment B raw666 raw666Labels = mixedMoment B raw666step0 raw666step0Labels := by
      have ha : raw666step0 = (fun i j => raw666 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw666step0 raw666; decide +kernel
      have hl : raw666step0Labels = raw666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw666 raw666Labels permutation152 permutation4
    mixedMoment B raw666step0 raw666step0Labels = mixedMoment B raw666step1 raw666step1Labels := by
      have ha : raw666step1 = raw666step0 := by apply Matrix.ext; unfold raw666step1 raw666step0; decide +kernel
      have hl : raw666step0Labels = labelEmbedding7 ∘ raw666step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw666step0 raw666step0Labels raw666step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4098 node4098Labels := by rfl

def raw667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw667step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw667 raw667Labels = mixedMoment B node535 node535Labels := by
  calc
    mixedMoment B raw667 raw667Labels = mixedMoment B raw667step0 raw667step0Labels := by
      have ha : raw667step0 = (fun i j => raw667 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw667step0 raw667; decide +kernel
      have hl : raw667step0Labels = raw667Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw667 raw667Labels permutation152 permutation4
    _ = mixedMoment B node535 node535Labels := by rfl

def raw668 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw668Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw668step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw668step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw668step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw668 raw668Labels = mixedMoment B node656 node656Labels := by
  calc
    mixedMoment B raw668 raw668Labels = mixedMoment B raw668step0 raw668step0Labels := by
      have ha : raw668step0 = (fun i j => raw668 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw668step0 raw668; decide +kernel
      have hl : raw668step0Labels = raw668Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw668 raw668Labels permutation182 permutation6
    mixedMoment B raw668step0 raw668step0Labels = mixedMoment B raw668step1 raw668step1Labels := by
      have ha : raw668step1 = -raw668step0 := by apply Matrix.ext; change ∀ i j, raw668step1 i j = -(raw668step0 i j); unfold raw668step1 raw668step0; decide +kernel
      have hl : raw668step1Labels = raw668step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw668step1 raw668step1Labels = mixedMoment B raw668step2 raw668step2Labels := by
      have ha : raw668step2 = raw668step1 := by apply Matrix.ext; unfold raw668step2 raw668step1; decide +kernel
      have hl : raw668step1Labels = labelEmbedding1 ∘ raw668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw668step1 raw668step1Labels raw668step2Labels labelEmbedding1 hl
    _ = mixedMoment B node656 node656Labels := by rfl

def raw669 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw669step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw669 raw669Labels = mixedMoment B node4099 node4099Labels := by
  calc
    mixedMoment B raw669 raw669Labels = mixedMoment B raw669step0 raw669step0Labels := by
      have ha : raw669step0 = (fun i j => raw669 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw669step0 raw669; decide +kernel
      have hl : raw669step0Labels = raw669Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw669 raw669Labels permutation32 permutation4
    mixedMoment B raw669step0 raw669step0Labels = mixedMoment B raw669step1 raw669step1Labels := by
      have ha : raw669step1 = raw669step0 := by apply Matrix.ext; unfold raw669step1 raw669step0; decide +kernel
      have hl : raw669step0Labels = labelEmbedding7 ∘ raw669step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw669step0 raw669step0Labels raw669step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4099 node4099Labels := by rfl

def raw670 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw670 raw670Labels = mixedMoment B node536 node536Labels := by
  calc
    mixedMoment B raw670 raw670Labels = mixedMoment B raw670step0 raw670step0Labels := by
      have ha : raw670step0 = (fun i j => raw670 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw670step0 raw670; decide +kernel
      have hl : raw670step0Labels = raw670Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw670 raw670Labels permutation32 permutation4
    _ = mixedMoment B node536 node536Labels := by rfl

def raw671 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw671Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw671step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw671step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw671step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw671 raw671Labels = mixedMoment B node657 node657Labels := by
  calc
    mixedMoment B raw671 raw671Labels = mixedMoment B raw671step0 raw671step0Labels := by
      have ha : raw671step0 = (fun i j => raw671 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw671step0 raw671; decide +kernel
      have hl : raw671step0Labels = raw671Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw671 raw671Labels permutation40 permutation6
    mixedMoment B raw671step0 raw671step0Labels = mixedMoment B raw671step1 raw671step1Labels := by
      have ha : raw671step1 = -raw671step0 := by apply Matrix.ext; change ∀ i j, raw671step1 i j = -(raw671step0 i j); unfold raw671step1 raw671step0; decide +kernel
      have hl : raw671step1Labels = raw671step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw671step1 raw671step1Labels = mixedMoment B raw671step2 raw671step2Labels := by
      have ha : raw671step2 = raw671step1 := by apply Matrix.ext; unfold raw671step2 raw671step1; decide +kernel
      have hl : raw671step1Labels = labelEmbedding1 ∘ raw671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw671step1 raw671step1Labels raw671step2Labels labelEmbedding1 hl
    _ = mixedMoment B node657 node657Labels := by rfl

def raw672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw672step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw672 raw672Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw672 raw672Labels = mixedMoment B raw672step0 raw672step0Labels := by
      have ha : raw672step0 = (fun i j => raw672 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw672step0 raw672; decide +kernel
      have hl : raw672step0Labels = raw672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw672 raw672Labels permutation152 permutation4
    mixedMoment B raw672step0 raw672step0Labels = mixedMoment B raw672step1 raw672step1Labels := by
      have ha : raw672step1 = raw672step0 := by apply Matrix.ext; unfold raw672step1 raw672step0; decide +kernel
      have hl : raw672step0Labels = labelEmbedding7 ∘ raw672step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw672step0 raw672step0Labels raw672step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4100 node4100Labels := by rfl

def raw673 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw673 raw673Labels = mixedMoment B node537 node537Labels := by
  calc
    mixedMoment B raw673 raw673Labels = mixedMoment B raw673step0 raw673step0Labels := by
      have ha : raw673step0 = (fun i j => raw673 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw673step0 raw673; decide +kernel
      have hl : raw673step0Labels = raw673Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw673 raw673Labels permutation152 permutation4
    _ = mixedMoment B node537 node537Labels := by rfl

def raw674 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw674Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw674step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw674step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw674step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw674 raw674Labels = mixedMoment B node662 node662Labels := by
  calc
    mixedMoment B raw674 raw674Labels = mixedMoment B raw674step0 raw674step0Labels := by
      have ha : raw674step0 = (fun i j => raw674 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw674step0 raw674; decide +kernel
      have hl : raw674step0Labels = raw674Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw674 raw674Labels permutation176 permutation6
    mixedMoment B raw674step0 raw674step0Labels = mixedMoment B raw674step1 raw674step1Labels := by
      have ha : raw674step1 = -raw674step0 := by apply Matrix.ext; change ∀ i j, raw674step1 i j = -(raw674step0 i j); unfold raw674step1 raw674step0; decide +kernel
      have hl : raw674step1Labels = raw674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw674step1 raw674step1Labels = mixedMoment B raw674step2 raw674step2Labels := by
      have ha : raw674step2 = raw674step1 := by apply Matrix.ext; unfold raw674step2 raw674step1; decide +kernel
      have hl : raw674step1Labels = labelEmbedding1 ∘ raw674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw674step1 raw674step1Labels raw674step2Labels labelEmbedding1 hl
    _ = mixedMoment B node662 node662Labels := by rfl

def raw675 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw675step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw675 raw675Labels = mixedMoment B node4101 node4101Labels := by
  calc
    mixedMoment B raw675 raw675Labels = mixedMoment B raw675step0 raw675step0Labels := by
      have ha : raw675step0 = (fun i j => raw675 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw675step0 raw675; decide +kernel
      have hl : raw675step0Labels = raw675Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw675 raw675Labels permutation32 permutation4
    mixedMoment B raw675step0 raw675step0Labels = mixedMoment B raw675step1 raw675step1Labels := by
      have ha : raw675step1 = raw675step0 := by apply Matrix.ext; unfold raw675step1 raw675step0; decide +kernel
      have hl : raw675step0Labels = labelEmbedding7 ∘ raw675step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw675step0 raw675step0Labels raw675step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4101 node4101Labels := by rfl

def raw676 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw676 raw676Labels = mixedMoment B node538 node538Labels := by
  calc
    mixedMoment B raw676 raw676Labels = mixedMoment B raw676step0 raw676step0Labels := by
      have ha : raw676step0 = (fun i j => raw676 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw676step0 raw676; decide +kernel
      have hl : raw676step0Labels = raw676Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw676 raw676Labels permutation32 permutation4
    _ = mixedMoment B node538 node538Labels := by rfl

def raw677 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw677Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw677step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw677step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw677 raw677Labels = mixedMoment B node663 node663Labels := by
  calc
    mixedMoment B raw677 raw677Labels = mixedMoment B raw677step0 raw677step0Labels := by
      have ha : raw677step0 = (fun i j => raw677 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw677step0 raw677; decide +kernel
      have hl : raw677step0Labels = raw677Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw677 raw677Labels permutation38 permutation6
    mixedMoment B raw677step0 raw677step0Labels = mixedMoment B raw677step1 raw677step1Labels := by
      have ha : raw677step1 = -raw677step0 := by apply Matrix.ext; change ∀ i j, raw677step1 i j = -(raw677step0 i j); unfold raw677step1 raw677step0; decide +kernel
      have hl : raw677step1Labels = raw677step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw677step1 raw677step1Labels = mixedMoment B raw677step2 raw677step2Labels := by
      have ha : raw677step2 = raw677step1 := by apply Matrix.ext; unfold raw677step2 raw677step1; decide +kernel
      have hl : raw677step1Labels = labelEmbedding1 ∘ raw677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw677step1 raw677step1Labels raw677step2Labels labelEmbedding1 hl
    _ = mixedMoment B node663 node663Labels := by rfl

def raw678 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw678step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw678 raw678Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw678 raw678Labels = mixedMoment B raw678step0 raw678step0Labels := by
      have ha : raw678step0 = (fun i j => raw678 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw678step0 raw678; decide +kernel
      have hl : raw678step0Labels = raw678Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw678 raw678Labels permutation32 permutation4
    mixedMoment B raw678step0 raw678step0Labels = mixedMoment B raw678step1 raw678step1Labels := by
      have ha : raw678step1 = raw678step0 := by apply Matrix.ext; unfold raw678step1 raw678step0; decide +kernel
      have hl : raw678step0Labels = labelEmbedding7 ∘ raw678step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw678step0 raw678step0Labels raw678step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4102 node4102Labels := by rfl

def raw679 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw679 raw679Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw679 raw679Labels = mixedMoment B raw679step0 raw679step0Labels := by
      have ha : raw679step0 = (fun i j => raw679 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw679step0 raw679; decide +kernel
      have hl : raw679step0Labels = raw679Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw679 raw679Labels permutation32 permutation4
    _ = mixedMoment B node539 node539Labels := by rfl

def raw680 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw680Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw680step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw680step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw680 raw680Labels = mixedMoment B node664 node664Labels := by
  calc
    mixedMoment B raw680 raw680Labels = mixedMoment B raw680step0 raw680step0Labels := by
      have ha : raw680step0 = (fun i j => raw680 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw680step0 raw680; decide +kernel
      have hl : raw680step0Labels = raw680Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw680 raw680Labels permutation38 permutation6
    mixedMoment B raw680step0 raw680step0Labels = mixedMoment B raw680step1 raw680step1Labels := by
      have ha : raw680step1 = -raw680step0 := by apply Matrix.ext; change ∀ i j, raw680step1 i j = -(raw680step0 i j); unfold raw680step1 raw680step0; decide +kernel
      have hl : raw680step1Labels = raw680step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw680step1 raw680step1Labels = mixedMoment B raw680step2 raw680step2Labels := by
      have ha : raw680step2 = raw680step1 := by apply Matrix.ext; unfold raw680step2 raw680step1; decide +kernel
      have hl : raw680step1Labels = labelEmbedding1 ∘ raw680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw680step1 raw680step1Labels raw680step2Labels labelEmbedding1 hl
    _ = mixedMoment B node664 node664Labels := by rfl

def raw681 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw681step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw681step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw681 raw681Labels = mixedMoment B node4103 node4103Labels := by
  calc
    mixedMoment B raw681 raw681Labels = mixedMoment B raw681step0 raw681step0Labels := by
      have ha : raw681step0 = (fun i j => raw681 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw681step0 raw681; decide +kernel
      have hl : raw681step0Labels = raw681Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw681 raw681Labels permutation8 permutation4
    mixedMoment B raw681step0 raw681step0Labels = mixedMoment B raw681step1 raw681step1Labels := by
      have ha : raw681step1 = raw681step0 := by apply Matrix.ext; unfold raw681step1 raw681step0; decide +kernel
      have hl : raw681step0Labels = labelEmbedding7 ∘ raw681step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw681step0 raw681step0Labels raw681step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4103 node4103Labels := by rfl

def raw682 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw682step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw682 raw682Labels = mixedMoment B node540 node540Labels := by
  calc
    mixedMoment B raw682 raw682Labels = mixedMoment B raw682step0 raw682step0Labels := by
      have ha : raw682step0 = (fun i j => raw682 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw682step0 raw682; decide +kernel
      have hl : raw682step0Labels = raw682Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw682 raw682Labels permutation8 permutation4
    _ = mixedMoment B node540 node540Labels := by rfl

def raw683 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw683Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw683step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw683step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw683step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw683 raw683Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw683 raw683Labels = mixedMoment B raw683step0 raw683step0Labels := by
      have ha : raw683step0 = (fun i j => raw683 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw683step0 raw683; decide +kernel
      have hl : raw683step0Labels = raw683Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw683 raw683Labels permutation10 permutation6
    mixedMoment B raw683step0 raw683step0Labels = mixedMoment B raw683step1 raw683step1Labels := by
      have ha : raw683step1 = -raw683step0 := by apply Matrix.ext; change ∀ i j, raw683step1 i j = -(raw683step0 i j); unfold raw683step1 raw683step0; decide +kernel
      have hl : raw683step1Labels = raw683step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw683step1 raw683step1Labels = mixedMoment B raw683step2 raw683step2Labels := by
      have ha : raw683step2 = raw683step1 := by apply Matrix.ext; unfold raw683step2 raw683step1; decide +kernel
      have hl : raw683step1Labels = labelEmbedding1 ∘ raw683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw683step1 raw683step1Labels raw683step2Labels labelEmbedding1 hl
    _ = mixedMoment B node665 node665Labels := by rfl

def raw684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw684step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw684 raw684Labels = mixedMoment B node4104 node4104Labels := by
  calc
    mixedMoment B raw684 raw684Labels = mixedMoment B raw684step0 raw684step0Labels := by
      have ha : raw684step0 = (fun i j => raw684 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw684step0 raw684; decide +kernel
      have hl : raw684step0Labels = raw684Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw684 raw684Labels permutation152 permutation4
    mixedMoment B raw684step0 raw684step0Labels = mixedMoment B raw684step1 raw684step1Labels := by
      have ha : raw684step1 = raw684step0 := by apply Matrix.ext; unfold raw684step1 raw684step0; decide +kernel
      have hl : raw684step0Labels = labelEmbedding7 ∘ raw684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw684step0 raw684step0Labels raw684step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4104 node4104Labels := by rfl

def raw685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw685 raw685Labels = mixedMoment B node541 node541Labels := by
  calc
    mixedMoment B raw685 raw685Labels = mixedMoment B raw685step0 raw685step0Labels := by
      have ha : raw685step0 = (fun i j => raw685 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw685step0 raw685; decide +kernel
      have hl : raw685step0Labels = raw685Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw685 raw685Labels permutation152 permutation4
    _ = mixedMoment B node541 node541Labels := by rfl

def raw686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw686Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw686step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw686step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw686step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw686 raw686Labels = mixedMoment B node674 node674Labels := by
  calc
    mixedMoment B raw686 raw686Labels = mixedMoment B raw686step0 raw686step0Labels := by
      have ha : raw686step0 = (fun i j => raw686 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw686step0 raw686; decide +kernel
      have hl : raw686step0Labels = raw686Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw686 raw686Labels permutation246 permutation6
    mixedMoment B raw686step0 raw686step0Labels = mixedMoment B raw686step1 raw686step1Labels := by
      have ha : raw686step1 = -raw686step0 := by apply Matrix.ext; change ∀ i j, raw686step1 i j = -(raw686step0 i j); unfold raw686step1 raw686step0; decide +kernel
      have hl : raw686step1Labels = raw686step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw686step1 raw686step1Labels = mixedMoment B raw686step2 raw686step2Labels := by
      have ha : raw686step2 = raw686step1 := by apply Matrix.ext; unfold raw686step2 raw686step1; decide +kernel
      have hl : raw686step1Labels = labelEmbedding1 ∘ raw686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw686step1 raw686step1Labels raw686step2Labels labelEmbedding1 hl
    _ = mixedMoment B node674 node674Labels := by rfl

def raw687 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw687step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw687step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw687 raw687Labels = mixedMoment B node4105 node4105Labels := by
  calc
    mixedMoment B raw687 raw687Labels = mixedMoment B raw687step0 raw687step0Labels := by
      have ha : raw687step0 = (fun i j => raw687 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw687step0 raw687; decide +kernel
      have hl : raw687step0Labels = raw687Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw687 raw687Labels permutation32 permutation4
    mixedMoment B raw687step0 raw687step0Labels = mixedMoment B raw687step1 raw687step1Labels := by
      have ha : raw687step1 = raw687step0 := by apply Matrix.ext; unfold raw687step1 raw687step0; decide +kernel
      have hl : raw687step0Labels = labelEmbedding7 ∘ raw687step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw687step0 raw687step0Labels raw687step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4105 node4105Labels := by rfl

def raw688 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw688 raw688Labels = mixedMoment B node542 node542Labels := by
  calc
    mixedMoment B raw688 raw688Labels = mixedMoment B raw688step0 raw688step0Labels := by
      have ha : raw688step0 = (fun i j => raw688 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw688step0 raw688; decide +kernel
      have hl : raw688step0Labels = raw688Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw688 raw688Labels permutation32 permutation4
    _ = mixedMoment B node542 node542Labels := by rfl

def raw689 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw689Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw689step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw689step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw689 raw689Labels = mixedMoment B node681 node681Labels := by
  calc
    mixedMoment B raw689 raw689Labels = mixedMoment B raw689step0 raw689step0Labels := by
      have ha : raw689step0 = (fun i j => raw689 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw689step0 raw689; decide +kernel
      have hl : raw689step0Labels = raw689Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw689 raw689Labels permutation32 permutation6
    mixedMoment B raw689step0 raw689step0Labels = mixedMoment B raw689step1 raw689step1Labels := by
      have ha : raw689step1 = -raw689step0 := by apply Matrix.ext; change ∀ i j, raw689step1 i j = -(raw689step0 i j); unfold raw689step1 raw689step0; decide +kernel
      have hl : raw689step1Labels = raw689step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw689step1 raw689step1Labels = mixedMoment B raw689step2 raw689step2Labels := by
      have ha : raw689step2 = raw689step1 := by apply Matrix.ext; unfold raw689step2 raw689step1; decide +kernel
      have hl : raw689step1Labels = labelEmbedding1 ∘ raw689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw689step1 raw689step1Labels raw689step2Labels labelEmbedding1 hl
    _ = mixedMoment B node681 node681Labels := by rfl

def raw690 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw690step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw690 raw690Labels = mixedMoment B node4106 node4106Labels := by
  calc
    mixedMoment B raw690 raw690Labels = mixedMoment B raw690step0 raw690step0Labels := by
      have ha : raw690step0 = (fun i j => raw690 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw690step0 raw690; decide +kernel
      have hl : raw690step0Labels = raw690Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw690 raw690Labels permutation32 permutation4
    mixedMoment B raw690step0 raw690step0Labels = mixedMoment B raw690step1 raw690step1Labels := by
      have ha : raw690step1 = raw690step0 := by apply Matrix.ext; unfold raw690step1 raw690step0; decide +kernel
      have hl : raw690step0Labels = labelEmbedding7 ∘ raw690step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw690step0 raw690step0Labels raw690step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4106 node4106Labels := by rfl

def raw691 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw691 raw691Labels = mixedMoment B node543 node543Labels := by
  calc
    mixedMoment B raw691 raw691Labels = mixedMoment B raw691step0 raw691step0Labels := by
      have ha : raw691step0 = (fun i j => raw691 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw691step0 raw691; decide +kernel
      have hl : raw691step0Labels = raw691Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw691 raw691Labels permutation32 permutation4
    _ = mixedMoment B node543 node543Labels := by rfl

def raw692 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw692Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw692step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw692step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw692 raw692Labels = mixedMoment B node675 node675Labels := by
  calc
    mixedMoment B raw692 raw692Labels = mixedMoment B raw692step0 raw692step0Labels := by
      have ha : raw692step0 = (fun i j => raw692 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw692step0 raw692; decide +kernel
      have hl : raw692step0Labels = raw692Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw692 raw692Labels permutation44 permutation6
    mixedMoment B raw692step0 raw692step0Labels = mixedMoment B raw692step1 raw692step1Labels := by
      have ha : raw692step1 = -raw692step0 := by apply Matrix.ext; change ∀ i j, raw692step1 i j = -(raw692step0 i j); unfold raw692step1 raw692step0; decide +kernel
      have hl : raw692step1Labels = raw692step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw692step1 raw692step1Labels = mixedMoment B raw692step2 raw692step2Labels := by
      have ha : raw692step2 = raw692step1 := by apply Matrix.ext; unfold raw692step2 raw692step1; decide +kernel
      have hl : raw692step1Labels = labelEmbedding1 ∘ raw692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw692step1 raw692step1Labels raw692step2Labels labelEmbedding1 hl
    _ = mixedMoment B node675 node675Labels := by rfl

def raw693 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw693step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw693 raw693Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw693 raw693Labels = mixedMoment B raw693step0 raw693step0Labels := by
      have ha : raw693step0 = (fun i j => raw693 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw693step0 raw693; decide +kernel
      have hl : raw693step0Labels = raw693Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw693 raw693Labels permutation32 permutation4
    mixedMoment B raw693step0 raw693step0Labels = mixedMoment B raw693step1 raw693step1Labels := by
      have ha : raw693step1 = raw693step0 := by apply Matrix.ext; unfold raw693step1 raw693step0; decide +kernel
      have hl : raw693step0Labels = labelEmbedding7 ∘ raw693step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw693step0 raw693step0Labels raw693step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4107 node4107Labels := by rfl

def raw694 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw694 raw694Labels = mixedMoment B node544 node544Labels := by
  calc
    mixedMoment B raw694 raw694Labels = mixedMoment B raw694step0 raw694step0Labels := by
      have ha : raw694step0 = (fun i j => raw694 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw694step0 raw694; decide +kernel
      have hl : raw694step0Labels = raw694Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw694 raw694Labels permutation32 permutation4
    _ = mixedMoment B node544 node544Labels := by rfl

def raw695 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw695Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw695step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw695step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw695 raw695Labels = mixedMoment B node682 node682Labels := by
  calc
    mixedMoment B raw695 raw695Labels = mixedMoment B raw695step0 raw695step0Labels := by
      have ha : raw695step0 = (fun i j => raw695 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw695step0 raw695; decide +kernel
      have hl : raw695step0Labels = raw695Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw695 raw695Labels permutation32 permutation6
    mixedMoment B raw695step0 raw695step0Labels = mixedMoment B raw695step1 raw695step1Labels := by
      have ha : raw695step1 = -raw695step0 := by apply Matrix.ext; change ∀ i j, raw695step1 i j = -(raw695step0 i j); unfold raw695step1 raw695step0; decide +kernel
      have hl : raw695step1Labels = raw695step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw695step1 raw695step1Labels = mixedMoment B raw695step2 raw695step2Labels := by
      have ha : raw695step2 = raw695step1 := by apply Matrix.ext; unfold raw695step2 raw695step1; decide +kernel
      have hl : raw695step1Labels = labelEmbedding1 ∘ raw695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw695step1 raw695step1Labels raw695step2Labels labelEmbedding1 hl
    _ = mixedMoment B node682 node682Labels := by rfl

def raw696 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw696step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw696step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw696 raw696Labels = mixedMoment B node4108 node4108Labels := by
  calc
    mixedMoment B raw696 raw696Labels = mixedMoment B raw696step0 raw696step0Labels := by
      have ha : raw696step0 = (fun i j => raw696 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw696step0 raw696; decide +kernel
      have hl : raw696step0Labels = raw696Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw696 raw696Labels permutation8 permutation4
    mixedMoment B raw696step0 raw696step0Labels = mixedMoment B raw696step1 raw696step1Labels := by
      have ha : raw696step1 = raw696step0 := by apply Matrix.ext; unfold raw696step1 raw696step0; decide +kernel
      have hl : raw696step0Labels = labelEmbedding7 ∘ raw696step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw696step0 raw696step0Labels raw696step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4108 node4108Labels := by rfl

def raw697 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw697step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw697 raw697Labels = mixedMoment B node545 node545Labels := by
  calc
    mixedMoment B raw697 raw697Labels = mixedMoment B raw697step0 raw697step0Labels := by
      have ha : raw697step0 = (fun i j => raw697 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw697step0 raw697; decide +kernel
      have hl : raw697step0Labels = raw697Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw697 raw697Labels permutation8 permutation4
    _ = mixedMoment B node545 node545Labels := by rfl

def raw698 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw698Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw698step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw698step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw698 raw698Labels = mixedMoment B node683 node683Labels := by
  calc
    mixedMoment B raw698 raw698Labels = mixedMoment B raw698step0 raw698step0Labels := by
      have ha : raw698step0 = (fun i j => raw698 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw698step0 raw698; decide +kernel
      have hl : raw698step0Labels = raw698Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw698 raw698Labels permutation8 permutation6
    mixedMoment B raw698step0 raw698step0Labels = mixedMoment B raw698step1 raw698step1Labels := by
      have ha : raw698step1 = -raw698step0 := by apply Matrix.ext; change ∀ i j, raw698step1 i j = -(raw698step0 i j); unfold raw698step1 raw698step0; decide +kernel
      have hl : raw698step1Labels = raw698step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw698step1 raw698step1Labels = mixedMoment B raw698step2 raw698step2Labels := by
      have ha : raw698step2 = raw698step1 := by apply Matrix.ext; unfold raw698step2 raw698step1; decide +kernel
      have hl : raw698step1Labels = labelEmbedding1 ∘ raw698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw698step1 raw698step1Labels raw698step2Labels labelEmbedding1 hl
    _ = mixedMoment B node683 node683Labels := by rfl

def raw699 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw699step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw699 raw699Labels = mixedMoment B node4109 node4109Labels := by
  calc
    mixedMoment B raw699 raw699Labels = mixedMoment B raw699step0 raw699step0Labels := by
      have ha : raw699step0 = (fun i j => raw699 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw699step0 raw699; decide +kernel
      have hl : raw699step0Labels = raw699Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw699 raw699Labels permutation8 permutation4
    mixedMoment B raw699step0 raw699step0Labels = mixedMoment B raw699step1 raw699step1Labels := by
      have ha : raw699step1 = raw699step0 := by apply Matrix.ext; unfold raw699step1 raw699step0; decide +kernel
      have hl : raw699step0Labels = labelEmbedding7 ∘ raw699step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw699step0 raw699step0Labels raw699step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4109 node4109Labels := by rfl

def raw700 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw700step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw700 raw700Labels = mixedMoment B node546 node546Labels := by
  calc
    mixedMoment B raw700 raw700Labels = mixedMoment B raw700step0 raw700step0Labels := by
      have ha : raw700step0 = (fun i j => raw700 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw700step0 raw700; decide +kernel
      have hl : raw700step0Labels = raw700Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw700 raw700Labels permutation8 permutation4
    _ = mixedMoment B node546 node546Labels := by rfl

def raw701 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw701Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw701step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw701step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw701 raw701Labels = mixedMoment B node676 node676Labels := by
  calc
    mixedMoment B raw701 raw701Labels = mixedMoment B raw701step0 raw701step0Labels := by
      have ha : raw701step0 = (fun i j => raw701 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw701step0 raw701; decide +kernel
      have hl : raw701step0Labels = raw701Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw701 raw701Labels permutation10 permutation6
    mixedMoment B raw701step0 raw701step0Labels = mixedMoment B raw701step1 raw701step1Labels := by
      have ha : raw701step1 = -raw701step0 := by apply Matrix.ext; change ∀ i j, raw701step1 i j = -(raw701step0 i j); unfold raw701step1 raw701step0; decide +kernel
      have hl : raw701step1Labels = raw701step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw701step1 raw701step1Labels = mixedMoment B raw701step2 raw701step2Labels := by
      have ha : raw701step2 = raw701step1 := by apply Matrix.ext; unfold raw701step2 raw701step1; decide +kernel
      have hl : raw701step1Labels = labelEmbedding1 ∘ raw701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw701step1 raw701step1Labels raw701step2Labels labelEmbedding1 hl
    _ = mixedMoment B node676 node676Labels := by rfl

def raw702 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw702step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw702step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw702 raw702Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw702 raw702Labels = mixedMoment B raw702step0 raw702step0Labels := by
      have ha : raw702step0 = (fun i j => raw702 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw702step0 raw702; decide +kernel
      have hl : raw702step0Labels = raw702Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw702 raw702Labels permutation8 permutation4
    mixedMoment B raw702step0 raw702step0Labels = mixedMoment B raw702step1 raw702step1Labels := by
      have ha : raw702step1 = raw702step0 := by apply Matrix.ext; unfold raw702step1 raw702step0; decide +kernel
      have hl : raw702step0Labels = labelEmbedding7 ∘ raw702step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw702step0 raw702step0Labels raw702step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4110 node4110Labels := by rfl

def raw703 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw703step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw703 raw703Labels = mixedMoment B node547 node547Labels := by
  calc
    mixedMoment B raw703 raw703Labels = mixedMoment B raw703step0 raw703step0Labels := by
      have ha : raw703step0 = (fun i j => raw703 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw703step0 raw703; decide +kernel
      have hl : raw703step0Labels = raw703Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw703 raw703Labels permutation8 permutation4
    _ = mixedMoment B node547 node547Labels := by rfl

def raw704 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw704Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw704step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw704 raw704Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw704 raw704Labels = mixedMoment B raw704step0 raw704step0Labels := by
      have ha : raw704step0 = (fun i j => raw704 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw704step0 raw704; decide +kernel
      have hl : raw704step0Labels = raw704Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw704 raw704Labels permutation8 permutation6
    mixedMoment B raw704step0 raw704step0Labels = mixedMoment B raw704step1 raw704step1Labels := by
      have ha : raw704step1 = -raw704step0 := by apply Matrix.ext; change ∀ i j, raw704step1 i j = -(raw704step0 i j); unfold raw704step1 raw704step0; decide +kernel
      have hl : raw704step1Labels = raw704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw704step1 raw704step1Labels = mixedMoment B raw704step2 raw704step2Labels := by
      have ha : raw704step2 = raw704step1 := by apply Matrix.ext; unfold raw704step2 raw704step1; decide +kernel
      have hl : raw704step1Labels = labelEmbedding1 ∘ raw704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw704step1 raw704step1Labels raw704step2Labels labelEmbedding1 hl
    _ = mixedMoment B node684 node684Labels := by rfl

def raw705 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw705step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw705step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw705 raw705Labels = mixedMoment B node4111 node4111Labels := by
  calc
    mixedMoment B raw705 raw705Labels = mixedMoment B raw705step0 raw705step0Labels := by
      have ha : raw705step0 = (fun i j => raw705 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw705step0 raw705; decide +kernel
      have hl : raw705step0Labels = raw705Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw705 raw705Labels permutation8 permutation4
    mixedMoment B raw705step0 raw705step0Labels = mixedMoment B raw705step1 raw705step1Labels := by
      have ha : raw705step1 = raw705step0 := by apply Matrix.ext; unfold raw705step1 raw705step0; decide +kernel
      have hl : raw705step0Labels = labelEmbedding7 ∘ raw705step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw705step0 raw705step0Labels raw705step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4111 node4111Labels := by rfl

def raw706 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw706step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw706 raw706Labels = mixedMoment B node548 node548Labels := by
  calc
    mixedMoment B raw706 raw706Labels = mixedMoment B raw706step0 raw706step0Labels := by
      have ha : raw706step0 = (fun i j => raw706 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw706step0 raw706; decide +kernel
      have hl : raw706step0Labels = raw706Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw706 raw706Labels permutation8 permutation4
    _ = mixedMoment B node548 node548Labels := by rfl

def raw707 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw707Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw707step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw707step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw707 raw707Labels = mixedMoment B node685 node685Labels := by
  calc
    mixedMoment B raw707 raw707Labels = mixedMoment B raw707step0 raw707step0Labels := by
      have ha : raw707step0 = (fun i j => raw707 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw707step0 raw707; decide +kernel
      have hl : raw707step0Labels = raw707Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw707 raw707Labels permutation9 permutation6
    mixedMoment B raw707step0 raw707step0Labels = mixedMoment B raw707step1 raw707step1Labels := by
      have ha : raw707step1 = -raw707step0 := by apply Matrix.ext; change ∀ i j, raw707step1 i j = -(raw707step0 i j); unfold raw707step1 raw707step0; decide +kernel
      have hl : raw707step1Labels = raw707step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw707step1 raw707step1Labels = mixedMoment B raw707step2 raw707step2Labels := by
      have ha : raw707step2 = raw707step1 := by apply Matrix.ext; unfold raw707step2 raw707step1; decide +kernel
      have hl : raw707step1Labels = labelEmbedding1 ∘ raw707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw707step1 raw707step1Labels raw707step2Labels labelEmbedding1 hl
    _ = mixedMoment B node685 node685Labels := by rfl

def raw708 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 5, -3]]
def raw708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw708step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw708step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw708step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw708 raw708Labels = mixedMoment B node4112 node4112Labels := by
  calc
    mixedMoment B raw708 raw708Labels = mixedMoment B raw708step0 raw708step0Labels := by
      have ha : raw708step0 = (fun i j => raw708 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw708step0 raw708; decide +kernel
      have hl : raw708step0Labels = raw708Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw708 raw708Labels permutation2 permutation4
    mixedMoment B raw708step0 raw708step0Labels = mixedMoment B raw708step1 raw708step1Labels := by
      have ha : raw708step1 = raw708step0 := by apply Matrix.ext; unfold raw708step1 raw708step0; decide +kernel
      have hl : raw708step0Labels = labelEmbedding7 ∘ raw708step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw708step0 raw708step0Labels raw708step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4112 node4112Labels := by rfl

def raw709 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 5, -3]]
def raw709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw709step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw709 raw709Labels = mixedMoment B node549 node549Labels := by
  calc
    mixedMoment B raw709 raw709Labels = mixedMoment B raw709step0 raw709step0Labels := by
      have ha : raw709step0 = (fun i j => raw709 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw709step0 raw709; decide +kernel
      have hl : raw709step0Labels = raw709Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw709 raw709Labels permutation2 permutation4
    _ = mixedMoment B node549 node549Labels := by rfl

def raw710 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 5, -3]]
def raw710Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw710step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-3, -2, 5]]
def raw710step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw710step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw710step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw710 raw710Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw710 raw710Labels = mixedMoment B raw710step0 raw710step0Labels := by
      have ha : raw710step0 = (fun i j => raw710 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw710step0 raw710; decide +kernel
      have hl : raw710step0Labels = raw710Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw710 raw710Labels permutation2 permutation6
    mixedMoment B raw710step0 raw710step0Labels = mixedMoment B raw710step1 raw710step1Labels := by
      have ha : raw710step1 = -raw710step0 := by apply Matrix.ext; change ∀ i j, raw710step1 i j = -(raw710step0 i j); unfold raw710step1 raw710step0; decide +kernel
      have hl : raw710step1Labels = raw710step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw710step1 raw710step1Labels = mixedMoment B raw710step2 raw710step2Labels := by
      have ha : raw710step2 = raw710step1 := by apply Matrix.ext; unfold raw710step2 raw710step1; decide +kernel
      have hl : raw710step1Labels = labelEmbedding1 ∘ raw710step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw710step1 raw710step1Labels raw710step2Labels labelEmbedding1 hl
    _ = mixedMoment B node686 node686Labels := by rfl

def raw711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw711step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw711 raw711Labels = mixedMoment B node4113 node4113Labels := by
  calc
    mixedMoment B raw711 raw711Labels = mixedMoment B raw711step0 raw711step0Labels := by
      have ha : raw711step0 = (fun i j => raw711 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw711step0 raw711; decide +kernel
      have hl : raw711step0Labels = raw711Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw711 raw711Labels permutation152 permutation4
    mixedMoment B raw711step0 raw711step0Labels = mixedMoment B raw711step1 raw711step1Labels := by
      have ha : raw711step1 = raw711step0 := by apply Matrix.ext; unfold raw711step1 raw711step0; decide +kernel
      have hl : raw711step0Labels = labelEmbedding7 ∘ raw711step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw711step0 raw711step0Labels raw711step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4113 node4113Labels := by rfl

def raw712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw712step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw712 raw712Labels = mixedMoment B node550 node550Labels := by
  calc
    mixedMoment B raw712 raw712Labels = mixedMoment B raw712step0 raw712step0Labels := by
      have ha : raw712step0 = (fun i j => raw712 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw712step0 raw712; decide +kernel
      have hl : raw712step0Labels = raw712Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw712 raw712Labels permutation152 permutation4
    _ = mixedMoment B node550 node550Labels := by rfl

def raw713 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw713Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw713 raw713Labels = mixedMoment B node658 node658Labels := by
  calc
    mixedMoment B raw713 raw713Labels = mixedMoment B raw713step0 raw713step0Labels := by
      have ha : raw713step0 = (fun i j => raw713 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw713step0 raw713; decide +kernel
      have hl : raw713step0Labels = raw713Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw713 raw713Labels permutation152 permutation6
    mixedMoment B raw713step0 raw713step0Labels = mixedMoment B raw713step1 raw713step1Labels := by
      have ha : raw713step1 = -raw713step0 := by apply Matrix.ext; change ∀ i j, raw713step1 i j = -(raw713step0 i j); unfold raw713step1 raw713step0; decide +kernel
      have hl : raw713step1Labels = raw713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw713step1 raw713step1Labels = mixedMoment B raw713step2 raw713step2Labels := by
      have ha : raw713step2 = raw713step1 := by apply Matrix.ext; unfold raw713step2 raw713step1; decide +kernel
      have hl : raw713step1Labels = labelEmbedding1 ∘ raw713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw713step1 raw713step1Labels raw713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node658 node658Labels := by rfl

def raw714 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw714step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw714 raw714Labels = mixedMoment B node4114 node4114Labels := by
  calc
    mixedMoment B raw714 raw714Labels = mixedMoment B raw714step0 raw714step0Labels := by
      have ha : raw714step0 = (fun i j => raw714 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw714step0 raw714; decide +kernel
      have hl : raw714step0Labels = raw714Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw714 raw714Labels permutation32 permutation4
    mixedMoment B raw714step0 raw714step0Labels = mixedMoment B raw714step1 raw714step1Labels := by
      have ha : raw714step1 = raw714step0 := by apply Matrix.ext; unfold raw714step1 raw714step0; decide +kernel
      have hl : raw714step0Labels = labelEmbedding7 ∘ raw714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw714step0 raw714step0Labels raw714step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4114 node4114Labels := by rfl

def raw715 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw715 raw715Labels = mixedMoment B node551 node551Labels := by
  calc
    mixedMoment B raw715 raw715Labels = mixedMoment B raw715step0 raw715step0Labels := by
      have ha : raw715step0 = (fun i j => raw715 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw715step0 raw715; decide +kernel
      have hl : raw715step0Labels = raw715Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw715 raw715Labels permutation32 permutation4
    _ = mixedMoment B node551 node551Labels := by rfl

def raw716 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw716Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw716 raw716Labels = mixedMoment B node659 node659Labels := by
  calc
    mixedMoment B raw716 raw716Labels = mixedMoment B raw716step0 raw716step0Labels := by
      have ha : raw716step0 = (fun i j => raw716 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw716step0 raw716; decide +kernel
      have hl : raw716step0Labels = raw716Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw716 raw716Labels permutation32 permutation6
    mixedMoment B raw716step0 raw716step0Labels = mixedMoment B raw716step1 raw716step1Labels := by
      have ha : raw716step1 = -raw716step0 := by apply Matrix.ext; change ∀ i j, raw716step1 i j = -(raw716step0 i j); unfold raw716step1 raw716step0; decide +kernel
      have hl : raw716step1Labels = raw716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw716step1 raw716step1Labels = mixedMoment B raw716step2 raw716step2Labels := by
      have ha : raw716step2 = raw716step1 := by apply Matrix.ext; unfold raw716step2 raw716step1; decide +kernel
      have hl : raw716step1Labels = labelEmbedding1 ∘ raw716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw716step1 raw716step1Labels raw716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node659 node659Labels := by rfl

def raw717 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw717step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw717 raw717Labels = mixedMoment B node4115 node4115Labels := by
  calc
    mixedMoment B raw717 raw717Labels = mixedMoment B raw717step0 raw717step0Labels := by
      have ha : raw717step0 = (fun i j => raw717 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw717step0 raw717; decide +kernel
      have hl : raw717step0Labels = raw717Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw717 raw717Labels permutation32 permutation4
    mixedMoment B raw717step0 raw717step0Labels = mixedMoment B raw717step1 raw717step1Labels := by
      have ha : raw717step1 = raw717step0 := by apply Matrix.ext; unfold raw717step1 raw717step0; decide +kernel
      have hl : raw717step0Labels = labelEmbedding7 ∘ raw717step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw717step0 raw717step0Labels raw717step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4115 node4115Labels := by rfl

def raw718 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw718 raw718Labels = mixedMoment B node552 node552Labels := by
  calc
    mixedMoment B raw718 raw718Labels = mixedMoment B raw718step0 raw718step0Labels := by
      have ha : raw718step0 = (fun i j => raw718 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw718step0 raw718; decide +kernel
      have hl : raw718step0Labels = raw718Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw718 raw718Labels permutation32 permutation4
    _ = mixedMoment B node552 node552Labels := by rfl

def raw719 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw719Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw719 raw719Labels = mixedMoment B node660 node660Labels := by
  calc
    mixedMoment B raw719 raw719Labels = mixedMoment B raw719step0 raw719step0Labels := by
      have ha : raw719step0 = (fun i j => raw719 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw719step0 raw719; decide +kernel
      have hl : raw719step0Labels = raw719Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw719 raw719Labels permutation32 permutation6
    mixedMoment B raw719step0 raw719step0Labels = mixedMoment B raw719step1 raw719step1Labels := by
      have ha : raw719step1 = -raw719step0 := by apply Matrix.ext; change ∀ i j, raw719step1 i j = -(raw719step0 i j); unfold raw719step1 raw719step0; decide +kernel
      have hl : raw719step1Labels = raw719step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw719step1 raw719step1Labels = mixedMoment B raw719step2 raw719step2Labels := by
      have ha : raw719step2 = raw719step1 := by apply Matrix.ext; unfold raw719step2 raw719step1; decide +kernel
      have hl : raw719step1Labels = labelEmbedding1 ∘ raw719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw719step1 raw719step1Labels raw719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node660 node660Labels := by rfl

def raw720 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 3, -4]]
def raw720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw720step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw720step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw720 raw720Labels = mixedMoment B node4116 node4116Labels := by
  calc
    mixedMoment B raw720 raw720Labels = mixedMoment B raw720step0 raw720step0Labels := by
      have ha : raw720step0 = (fun i j => raw720 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw720step0 raw720; decide +kernel
      have hl : raw720step0Labels = raw720Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw720 raw720Labels permutation8 permutation4
    mixedMoment B raw720step0 raw720step0Labels = mixedMoment B raw720step1 raw720step1Labels := by
      have ha : raw720step1 = raw720step0 := by apply Matrix.ext; unfold raw720step1 raw720step0; decide +kernel
      have hl : raw720step0Labels = labelEmbedding7 ∘ raw720step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw720step0 raw720step0Labels raw720step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4116 node4116Labels := by rfl

def raw721 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 3, -4]]
def raw721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw721step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw721 raw721Labels = mixedMoment B node553 node553Labels := by
  calc
    mixedMoment B raw721 raw721Labels = mixedMoment B raw721step0 raw721step0Labels := by
      have ha : raw721step0 = (fun i j => raw721 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw721step0 raw721; decide +kernel
      have hl : raw721step0Labels = raw721Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw721 raw721Labels permutation8 permutation4
    _ = mixedMoment B node553 node553Labels := by rfl

def raw722 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 3, -4]]
def raw722Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw722step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-4, 1, 3]]
def raw722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def raw722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def raw722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw722 raw722Labels = mixedMoment B node661 node661Labels := by
  calc
    mixedMoment B raw722 raw722Labels = mixedMoment B raw722step0 raw722step0Labels := by
      have ha : raw722step0 = (fun i j => raw722 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw722step0 raw722; decide +kernel
      have hl : raw722step0Labels = raw722Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw722 raw722Labels permutation8 permutation6
    mixedMoment B raw722step0 raw722step0Labels = mixedMoment B raw722step1 raw722step1Labels := by
      have ha : raw722step1 = -raw722step0 := by apply Matrix.ext; change ∀ i j, raw722step1 i j = -(raw722step0 i j); unfold raw722step1 raw722step0; decide +kernel
      have hl : raw722step1Labels = raw722step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw722step1 raw722step1Labels = mixedMoment B raw722step2 raw722step2Labels := by
      have ha : raw722step2 = raw722step1 := by apply Matrix.ext; unfold raw722step2 raw722step1; decide +kernel
      have hl : raw722step1Labels = labelEmbedding1 ∘ raw722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw722step1 raw722step1Labels raw722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node661 node661Labels := by rfl

def raw723 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw723step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw723 raw723Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw723 raw723Labels = mixedMoment B raw723step0 raw723step0Labels := by
      have ha : raw723step0 = (fun i j => raw723 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw723step0 raw723; decide +kernel
      have hl : raw723step0Labels = raw723Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw723 raw723Labels permutation32 permutation4
    mixedMoment B raw723step0 raw723step0Labels = mixedMoment B raw723step1 raw723step1Labels := by
      have ha : raw723step1 = raw723step0 := by apply Matrix.ext; unfold raw723step1 raw723step0; decide +kernel
      have hl : raw723step0Labels = labelEmbedding7 ∘ raw723step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw723step0 raw723step0Labels raw723step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

def raw724 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw724 raw724Labels = mixedMoment B node554 node554Labels := by
  calc
    mixedMoment B raw724 raw724Labels = mixedMoment B raw724step0 raw724step0Labels := by
      have ha : raw724step0 = (fun i j => raw724 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw724step0 raw724; decide +kernel
      have hl : raw724step0Labels = raw724Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw724 raw724Labels permutation32 permutation4
    _ = mixedMoment B node554 node554Labels := by rfl

def raw725 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw725Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw725step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw725 raw725Labels = mixedMoment B node668 node668Labels := by
  calc
    mixedMoment B raw725 raw725Labels = mixedMoment B raw725step0 raw725step0Labels := by
      have ha : raw725step0 = (fun i j => raw725 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw725step0 raw725; decide +kernel
      have hl : raw725step0Labels = raw725Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw725 raw725Labels permutation33 permutation6
    mixedMoment B raw725step0 raw725step0Labels = mixedMoment B raw725step1 raw725step1Labels := by
      have ha : raw725step1 = -raw725step0 := by apply Matrix.ext; change ∀ i j, raw725step1 i j = -(raw725step0 i j); unfold raw725step1 raw725step0; decide +kernel
      have hl : raw725step1Labels = raw725step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw725step1 raw725step1Labels = mixedMoment B raw725step2 raw725step2Labels := by
      have ha : raw725step2 = raw725step1 := by apply Matrix.ext; unfold raw725step2 raw725step1; decide +kernel
      have hl : raw725step1Labels = labelEmbedding1 ∘ raw725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw725step1 raw725step1Labels raw725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node668 node668Labels := by rfl

def raw726 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw726step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw726step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw726 raw726Labels = mixedMoment B node4121 node4121Labels := by
  calc
    mixedMoment B raw726 raw726Labels = mixedMoment B raw726step0 raw726step0Labels := by
      have ha : raw726step0 = (fun i j => raw726 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw726step0 raw726; decide +kernel
      have hl : raw726step0Labels = raw726Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw726 raw726Labels permutation8 permutation4
    mixedMoment B raw726step0 raw726step0Labels = mixedMoment B raw726step1 raw726step1Labels := by
      have ha : raw726step1 = raw726step0 := by apply Matrix.ext; unfold raw726step1 raw726step0; decide +kernel
      have hl : raw726step0Labels = labelEmbedding7 ∘ raw726step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw726step0 raw726step0Labels raw726step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4121 node4121Labels := by rfl

def raw727 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw727step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw727 raw727Labels = mixedMoment B node555 node555Labels := by
  calc
    mixedMoment B raw727 raw727Labels = mixedMoment B raw727step0 raw727step0Labels := by
      have ha : raw727step0 = (fun i j => raw727 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw727step0 raw727; decide +kernel
      have hl : raw727step0Labels = raw727Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw727 raw727Labels permutation8 permutation4
    _ = mixedMoment B node555 node555Labels := by rfl

def raw728 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw728Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw728step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw728 raw728Labels = mixedMoment B node671 node671Labels := by
  calc
    mixedMoment B raw728 raw728Labels = mixedMoment B raw728step0 raw728step0Labels := by
      have ha : raw728step0 = (fun i j => raw728 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw728step0 raw728; decide +kernel
      have hl : raw728step0Labels = raw728Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw728 raw728Labels permutation8 permutation6
    mixedMoment B raw728step0 raw728step0Labels = mixedMoment B raw728step1 raw728step1Labels := by
      have ha : raw728step1 = -raw728step0 := by apply Matrix.ext; change ∀ i j, raw728step1 i j = -(raw728step0 i j); unfold raw728step1 raw728step0; decide +kernel
      have hl : raw728step1Labels = raw728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw728step1 raw728step1Labels = mixedMoment B raw728step2 raw728step2Labels := by
      have ha : raw728step2 = raw728step1 := by apply Matrix.ext; unfold raw728step2 raw728step1; decide +kernel
      have hl : raw728step1Labels = labelEmbedding1 ∘ raw728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw728step1 raw728step1Labels raw728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node671 node671Labels := by rfl

def raw729 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw729step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw729step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw729step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw729 raw729Labels = mixedMoment B node4122 node4122Labels := by
  calc
    mixedMoment B raw729 raw729Labels = mixedMoment B raw729step0 raw729step0Labels := by
      have ha : raw729step0 = (fun i j => raw729 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw729step0 raw729; decide +kernel
      have hl : raw729step0Labels = raw729Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw729 raw729Labels permutation8 permutation4
    mixedMoment B raw729step0 raw729step0Labels = mixedMoment B raw729step1 raw729step1Labels := by
      have ha : raw729step1 = raw729step0 := by apply Matrix.ext; unfold raw729step1 raw729step0; decide +kernel
      have hl : raw729step0Labels = labelEmbedding7 ∘ raw729step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw729step0 raw729step0Labels raw729step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4122 node4122Labels := by rfl

def raw730 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw730step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw730 raw730Labels = mixedMoment B node556 node556Labels := by
  calc
    mixedMoment B raw730 raw730Labels = mixedMoment B raw730step0 raw730step0Labels := by
      have ha : raw730step0 = (fun i j => raw730 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw730step0 raw730; decide +kernel
      have hl : raw730step0Labels = raw730Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw730 raw730Labels permutation8 permutation4
    _ = mixedMoment B node556 node556Labels := by rfl

def raw731 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw731Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw731step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw731 raw731Labels = mixedMoment B node670 node670Labels := by
  calc
    mixedMoment B raw731 raw731Labels = mixedMoment B raw731step0 raw731step0Labels := by
      have ha : raw731step0 = (fun i j => raw731 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw731step0 raw731; decide +kernel
      have hl : raw731step0Labels = raw731Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw731 raw731Labels permutation8 permutation6
    mixedMoment B raw731step0 raw731step0Labels = mixedMoment B raw731step1 raw731step1Labels := by
      have ha : raw731step1 = -raw731step0 := by apply Matrix.ext; change ∀ i j, raw731step1 i j = -(raw731step0 i j); unfold raw731step1 raw731step0; decide +kernel
      have hl : raw731step1Labels = raw731step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw731step1 raw731step1Labels = mixedMoment B raw731step2 raw731step2Labels := by
      have ha : raw731step2 = raw731step1 := by apply Matrix.ext; unfold raw731step2 raw731step1; decide +kernel
      have hl : raw731step1Labels = labelEmbedding1 ∘ raw731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw731step1 raw731step1Labels raw731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node670 node670Labels := by rfl

def raw732 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw732step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw732step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw732 raw732Labels = mixedMoment B node4126 node4126Labels := by
  calc
    mixedMoment B raw732 raw732Labels = mixedMoment B raw732step0 raw732step0Labels := by
      have ha : raw732step0 = (fun i j => raw732 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw732step0 raw732; decide +kernel
      have hl : raw732step0Labels = raw732Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw732 raw732Labels permutation32 permutation4
    mixedMoment B raw732step0 raw732step0Labels = mixedMoment B raw732step1 raw732step1Labels := by
      have ha : raw732step1 = raw732step0 := by apply Matrix.ext; unfold raw732step1 raw732step0; decide +kernel
      have hl : raw732step0Labels = labelEmbedding7 ∘ raw732step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw732step0 raw732step0Labels raw732step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4126 node4126Labels := by rfl

def raw733 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw733 raw733Labels = mixedMoment B node557 node557Labels := by
  calc
    mixedMoment B raw733 raw733Labels = mixedMoment B raw733step0 raw733step0Labels := by
      have ha : raw733step0 = (fun i j => raw733 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw733step0 raw733; decide +kernel
      have hl : raw733step0Labels = raw733Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw733 raw733Labels permutation32 permutation4
    _ = mixedMoment B node557 node557Labels := by rfl

def raw734 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw734Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw734 raw734Labels = mixedMoment B node677 node677Labels := by
  calc
    mixedMoment B raw734 raw734Labels = mixedMoment B raw734step0 raw734step0Labels := by
      have ha : raw734step0 = (fun i j => raw734 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw734step0 raw734; decide +kernel
      have hl : raw734step0Labels = raw734Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw734 raw734Labels permutation50 permutation6
    mixedMoment B raw734step0 raw734step0Labels = mixedMoment B raw734step1 raw734step1Labels := by
      have ha : raw734step1 = -raw734step0 := by apply Matrix.ext; change ∀ i j, raw734step1 i j = -(raw734step0 i j); unfold raw734step1 raw734step0; decide +kernel
      have hl : raw734step1Labels = raw734step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw734step1 raw734step1Labels = mixedMoment B raw734step2 raw734step2Labels := by
      have ha : raw734step2 = raw734step1 := by apply Matrix.ext; unfold raw734step2 raw734step1; decide +kernel
      have hl : raw734step1Labels = labelEmbedding1 ∘ raw734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw734step1 raw734step1Labels raw734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node677 node677Labels := by rfl

def raw735 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw735step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw735step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw735 raw735Labels = mixedMoment B node4128 node4128Labels := by
  calc
    mixedMoment B raw735 raw735Labels = mixedMoment B raw735step0 raw735step0Labels := by
      have ha : raw735step0 = (fun i j => raw735 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw735step0 raw735; decide +kernel
      have hl : raw735step0Labels = raw735Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw735 raw735Labels permutation8 permutation4
    mixedMoment B raw735step0 raw735step0Labels = mixedMoment B raw735step1 raw735step1Labels := by
      have ha : raw735step1 = raw735step0 := by apply Matrix.ext; unfold raw735step1 raw735step0; decide +kernel
      have hl : raw735step0Labels = labelEmbedding7 ∘ raw735step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw735step0 raw735step0Labels raw735step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4128 node4128Labels := by rfl

def raw736 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw736step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw736 raw736Labels = mixedMoment B node559 node559Labels := by
  calc
    mixedMoment B raw736 raw736Labels = mixedMoment B raw736step0 raw736step0Labels := by
      have ha : raw736step0 = (fun i j => raw736 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw736step0 raw736; decide +kernel
      have hl : raw736step0Labels = raw736Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw736 raw736Labels permutation8 permutation4
    _ = mixedMoment B node559 node559Labels := by rfl

def raw737 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw737Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw737step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw737step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw737 raw737Labels = mixedMoment B node690 node690Labels := by
  calc
    mixedMoment B raw737 raw737Labels = mixedMoment B raw737step0 raw737step0Labels := by
      have ha : raw737step0 = (fun i j => raw737 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw737step0 raw737; decide +kernel
      have hl : raw737step0Labels = raw737Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw737 raw737Labels permutation9 permutation6
    mixedMoment B raw737step0 raw737step0Labels = mixedMoment B raw737step1 raw737step1Labels := by
      have ha : raw737step1 = -raw737step0 := by apply Matrix.ext; change ∀ i j, raw737step1 i j = -(raw737step0 i j); unfold raw737step1 raw737step0; decide +kernel
      have hl : raw737step1Labels = raw737step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw737step1 raw737step1Labels = mixedMoment B raw737step2 raw737step2Labels := by
      have ha : raw737step2 = raw737step1 := by apply Matrix.ext; unfold raw737step2 raw737step1; decide +kernel
      have hl : raw737step1Labels = labelEmbedding1 ∘ raw737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw737step1 raw737step1Labels raw737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node690 node690Labels := by rfl

def raw738 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw738step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw738step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw738 raw738Labels = mixedMoment B node4129 node4129Labels := by
  calc
    mixedMoment B raw738 raw738Labels = mixedMoment B raw738step0 raw738step0Labels := by
      have ha : raw738step0 = (fun i j => raw738 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw738step0 raw738; decide +kernel
      have hl : raw738step0Labels = raw738Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw738 raw738Labels permutation8 permutation4
    mixedMoment B raw738step0 raw738step0Labels = mixedMoment B raw738step1 raw738step1Labels := by
      have ha : raw738step1 = raw738step0 := by apply Matrix.ext; unfold raw738step1 raw738step0; decide +kernel
      have hl : raw738step0Labels = labelEmbedding7 ∘ raw738step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw738step0 raw738step0Labels raw738step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4129 node4129Labels := by rfl

def raw739 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw739step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw739 raw739Labels = mixedMoment B node560 node560Labels := by
  calc
    mixedMoment B raw739 raw739Labels = mixedMoment B raw739step0 raw739step0Labels := by
      have ha : raw739step0 = (fun i j => raw739 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw739step0 raw739; decide +kernel
      have hl : raw739step0Labels = raw739Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw739 raw739Labels permutation8 permutation4
    _ = mixedMoment B node560 node560Labels := by rfl

def raw740 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw740Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw740step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw740step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw740step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw740 raw740Labels = mixedMoment B node678 node678Labels := by
  calc
    mixedMoment B raw740 raw740Labels = mixedMoment B raw740step0 raw740step0Labels := by
      have ha : raw740step0 = (fun i j => raw740 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw740step0 raw740; decide +kernel
      have hl : raw740step0Labels = raw740Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw740 raw740Labels permutation10 permutation6
    mixedMoment B raw740step0 raw740step0Labels = mixedMoment B raw740step1 raw740step1Labels := by
      have ha : raw740step1 = -raw740step0 := by apply Matrix.ext; change ∀ i j, raw740step1 i j = -(raw740step0 i j); unfold raw740step1 raw740step0; decide +kernel
      have hl : raw740step1Labels = raw740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw740step1 raw740step1Labels = mixedMoment B raw740step2 raw740step2Labels := by
      have ha : raw740step2 = raw740step1 := by apply Matrix.ext; unfold raw740step2 raw740step1; decide +kernel
      have hl : raw740step1Labels = labelEmbedding1 ∘ raw740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw740step1 raw740step1Labels raw740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node678 node678Labels := by rfl

def raw741 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw741step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw741step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw741 raw741Labels = mixedMoment B node4132 node4132Labels := by
  calc
    mixedMoment B raw741 raw741Labels = mixedMoment B raw741step0 raw741step0Labels := by
      have ha : raw741step0 = (fun i j => raw741 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw741step0 raw741; decide +kernel
      have hl : raw741step0Labels = raw741Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw741 raw741Labels permutation8 permutation4
    mixedMoment B raw741step0 raw741step0Labels = mixedMoment B raw741step1 raw741step1Labels := by
      have ha : raw741step1 = raw741step0 := by apply Matrix.ext; unfold raw741step1 raw741step0; decide +kernel
      have hl : raw741step0Labels = labelEmbedding7 ∘ raw741step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw741step0 raw741step0Labels raw741step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4132 node4132Labels := by rfl

def raw742 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw742step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw742 raw742Labels = mixedMoment B node562 node562Labels := by
  calc
    mixedMoment B raw742 raw742Labels = mixedMoment B raw742step0 raw742step0Labels := by
      have ha : raw742step0 = (fun i j => raw742 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw742step0 raw742; decide +kernel
      have hl : raw742step0Labels = raw742Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw742 raw742Labels permutation8 permutation4
    _ = mixedMoment B node562 node562Labels := by rfl

def raw743 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw743Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw743step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw743 raw743Labels = mixedMoment B node679 node679Labels := by
  calc
    mixedMoment B raw743 raw743Labels = mixedMoment B raw743step0 raw743step0Labels := by
      have ha : raw743step0 = (fun i j => raw743 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw743step0 raw743; decide +kernel
      have hl : raw743step0Labels = raw743Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw743 raw743Labels permutation10 permutation6
    mixedMoment B raw743step0 raw743step0Labels = mixedMoment B raw743step1 raw743step1Labels := by
      have ha : raw743step1 = -raw743step0 := by apply Matrix.ext; change ∀ i j, raw743step1 i j = -(raw743step0 i j); unfold raw743step1 raw743step0; decide +kernel
      have hl : raw743step1Labels = raw743step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw743step1 raw743step1Labels = mixedMoment B raw743step2 raw743step2Labels := by
      have ha : raw743step2 = raw743step1 := by apply Matrix.ext; unfold raw743step2 raw743step1; decide +kernel
      have hl : raw743step1Labels = labelEmbedding1 ∘ raw743step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw743step1 raw743step1Labels raw743step2Labels labelEmbedding1 hl
    _ = mixedMoment B node679 node679Labels := by rfl

def raw744 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw744step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw744step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw744step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw744 raw744Labels = mixedMoment B node4133 node4133Labels := by
  calc
    mixedMoment B raw744 raw744Labels = mixedMoment B raw744step0 raw744step0Labels := by
      have ha : raw744step0 = (fun i j => raw744 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw744step0 raw744; decide +kernel
      have hl : raw744step0Labels = raw744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw744 raw744Labels permutation8 permutation4
    mixedMoment B raw744step0 raw744step0Labels = mixedMoment B raw744step1 raw744step1Labels := by
      have ha : raw744step1 = raw744step0 := by apply Matrix.ext; unfold raw744step1 raw744step0; decide +kernel
      have hl : raw744step0Labels = labelEmbedding7 ∘ raw744step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw744step0 raw744step0Labels raw744step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4133 node4133Labels := by rfl

def raw745 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw745step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw745 raw745Labels = mixedMoment B node563 node563Labels := by
  calc
    mixedMoment B raw745 raw745Labels = mixedMoment B raw745step0 raw745step0Labels := by
      have ha : raw745step0 = (fun i j => raw745 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw745step0 raw745; decide +kernel
      have hl : raw745step0Labels = raw745Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw745 raw745Labels permutation8 permutation4
    _ = mixedMoment B node563 node563Labels := by rfl

def raw746 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw746Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw746step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw746 raw746Labels = mixedMoment B node692 node692Labels := by
  calc
    mixedMoment B raw746 raw746Labels = mixedMoment B raw746step0 raw746step0Labels := by
      have ha : raw746step0 = (fun i j => raw746 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw746step0 raw746; decide +kernel
      have hl : raw746step0Labels = raw746Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw746 raw746Labels permutation11 permutation6
    mixedMoment B raw746step0 raw746step0Labels = mixedMoment B raw746step1 raw746step1Labels := by
      have ha : raw746step1 = -raw746step0 := by apply Matrix.ext; change ∀ i j, raw746step1 i j = -(raw746step0 i j); unfold raw746step1 raw746step0; decide +kernel
      have hl : raw746step1Labels = raw746step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw746step1 raw746step1Labels = mixedMoment B raw746step2 raw746step2Labels := by
      have ha : raw746step2 = raw746step1 := by apply Matrix.ext; unfold raw746step2 raw746step1; decide +kernel
      have hl : raw746step1Labels = labelEmbedding1 ∘ raw746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw746step1 raw746step1Labels raw746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node692 node692Labels := by rfl

def raw747 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 4, -2]]
def raw747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw747step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw747step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw747step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw747step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw747 raw747Labels = mixedMoment B node4134 node4134Labels := by
  calc
    mixedMoment B raw747 raw747Labels = mixedMoment B raw747step0 raw747step0Labels := by
      have ha : raw747step0 = (fun i j => raw747 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw747step0 raw747; decide +kernel
      have hl : raw747step0Labels = raw747Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw747 raw747Labels permutation2 permutation4
    mixedMoment B raw747step0 raw747step0Labels = mixedMoment B raw747step1 raw747step1Labels := by
      have ha : raw747step1 = raw747step0 := by apply Matrix.ext; unfold raw747step1 raw747step0; decide +kernel
      have hl : raw747step0Labels = labelEmbedding7 ∘ raw747step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw747step0 raw747step0Labels raw747step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4134 node4134Labels := by rfl

def raw748 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 4, -2]]
def raw748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw748step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw748 raw748Labels = mixedMoment B node564 node564Labels := by
  calc
    mixedMoment B raw748 raw748Labels = mixedMoment B raw748step0 raw748step0Labels := by
      have ha : raw748step0 = (fun i j => raw748 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw748step0 raw748; decide +kernel
      have hl : raw748step0Labels = raw748Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw748 raw748Labels permutation2 permutation4
    _ = mixedMoment B node564 node564Labels := by rfl

def raw749 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 4, -2]]
def raw749Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw749step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-2, 1, 1], ![-2, -2, 4]]
def raw749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw749step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, -1, -1], ![2, 2, -4]]
def raw749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw749step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, -1, -1], ![2, 2, -4]]
def raw749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw749 raw749Labels = mixedMoment B node695 node695Labels := by
  calc
    mixedMoment B raw749 raw749Labels = mixedMoment B raw749step0 raw749step0Labels := by
      have ha : raw749step0 = (fun i j => raw749 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw749step0 raw749; decide +kernel
      have hl : raw749step0Labels = raw749Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw749 raw749Labels permutation2 permutation6
    mixedMoment B raw749step0 raw749step0Labels = mixedMoment B raw749step1 raw749step1Labels := by
      have ha : raw749step1 = -raw749step0 := by apply Matrix.ext; change ∀ i j, raw749step1 i j = -(raw749step0 i j); unfold raw749step1 raw749step0; decide +kernel
      have hl : raw749step1Labels = raw749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw749step1 raw749step1Labels = mixedMoment B raw749step2 raw749step2Labels := by
      have ha : raw749step2 = raw749step1 := by apply Matrix.ext; unfold raw749step2 raw749step1; decide +kernel
      have hl : raw749step1Labels = labelEmbedding1 ∘ raw749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw749step1 raw749step1Labels raw749step2Labels labelEmbedding1 hl
    _ = mixedMoment B node695 node695Labels := by rfl

def raw750 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![-2, 2, 0], ![1, 3, -4]]
def raw750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw750step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw750step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw750step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw750 raw750Labels = mixedMoment B node4135 node4135Labels := by
  calc
    mixedMoment B raw750 raw750Labels = mixedMoment B raw750step0 raw750step0Labels := by
      have ha : raw750step0 = (fun i j => raw750 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw750step0 raw750; decide +kernel
      have hl : raw750step0Labels = raw750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw750 raw750Labels permutation2 permutation4
    mixedMoment B raw750step0 raw750step0Labels = mixedMoment B raw750step1 raw750step1Labels := by
      have ha : raw750step1 = raw750step0 := by apply Matrix.ext; unfold raw750step1 raw750step0; decide +kernel
      have hl : raw750step0Labels = labelEmbedding7 ∘ raw750step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw750step0 raw750step0Labels raw750step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4135 node4135Labels := by rfl

def raw751 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![-2, 2, 0], ![1, 3, -4]]
def raw751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw751step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw751 raw751Labels = mixedMoment B node565 node565Labels := by
  calc
    mixedMoment B raw751 raw751Labels = mixedMoment B raw751step0 raw751step0Labels := by
      have ha : raw751step0 = (fun i j => raw751 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw751step0 raw751; decide +kernel
      have hl : raw751step0Labels = raw751Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw751 raw751Labels permutation2 permutation4
    _ = mixedMoment B node565 node565Labels := by rfl

def raw752 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![-2, 2, 0], ![1, 3, -4]]
def raw752Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw752step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-4, 1, 3]]
def raw752step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw752step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![4, -1, -3]]
def raw752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw752step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![4, -1, -3]]
def raw752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw752 raw752Labels = mixedMoment B node680 node680Labels := by
  calc
    mixedMoment B raw752 raw752Labels = mixedMoment B raw752step0 raw752step0Labels := by
      have ha : raw752step0 = (fun i j => raw752 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw752step0 raw752; decide +kernel
      have hl : raw752step0Labels = raw752Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw752 raw752Labels permutation2 permutation6
    mixedMoment B raw752step0 raw752step0Labels = mixedMoment B raw752step1 raw752step1Labels := by
      have ha : raw752step1 = -raw752step0 := by apply Matrix.ext; change ∀ i j, raw752step1 i j = -(raw752step0 i j); unfold raw752step1 raw752step0; decide +kernel
      have hl : raw752step1Labels = raw752step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw752step1 raw752step1Labels = mixedMoment B raw752step2 raw752step2Labels := by
      have ha : raw752step2 = raw752step1 := by apply Matrix.ext; unfold raw752step2 raw752step1; decide +kernel
      have hl : raw752step1Labels = labelEmbedding1 ∘ raw752step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw752step1 raw752step1Labels raw752step2Labels labelEmbedding1 hl
    _ = mixedMoment B node680 node680Labels := by rfl

def raw753 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 2, -3], ![-2, 3, -1]]
def raw753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw753step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw753step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw753step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw753 raw753Labels = mixedMoment B node4138 node4138Labels := by
  calc
    mixedMoment B raw753 raw753Labels = mixedMoment B raw753step0 raw753step0Labels := by
      have ha : raw753step0 = (fun i j => raw753 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw753step0 raw753; decide +kernel
      have hl : raw753step0Labels = raw753Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw753 raw753Labels permutation2 permutation4
    mixedMoment B raw753step0 raw753step0Labels = mixedMoment B raw753step1 raw753step1Labels := by
      have ha : raw753step1 = raw753step0 := by apply Matrix.ext; unfold raw753step1 raw753step0; decide +kernel
      have hl : raw753step0Labels = labelEmbedding7 ∘ raw753step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw753step0 raw753step0Labels raw753step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4138 node4138Labels := by rfl

def raw754 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 2, -3], ![-2, 3, -1]]
def raw754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw754step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw754 raw754Labels = mixedMoment B node566 node566Labels := by
  calc
    mixedMoment B raw754 raw754Labels = mixedMoment B raw754step0 raw754step0Labels := by
      have ha : raw754step0 = (fun i j => raw754 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw754step0 raw754; decide +kernel
      have hl : raw754step0Labels = raw754Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw754 raw754Labels permutation2 permutation4
    _ = mixedMoment B node566 node566Labels := by rfl

def raw755 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 2, -3], ![-2, 3, -1]]
def raw755Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw755step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, -2, 3], ![-3, 1, 2]]
def raw755step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw755step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 2, -3], ![3, -1, -2]]
def raw755step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw755step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 2, -3], ![3, -1, -2]]
def raw755step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw755 raw755Labels = mixedMoment B node694 node694Labels := by
  calc
    mixedMoment B raw755 raw755Labels = mixedMoment B raw755step0 raw755step0Labels := by
      have ha : raw755step0 = (fun i j => raw755 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw755step0 raw755; decide +kernel
      have hl : raw755step0Labels = raw755Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw755 raw755Labels permutation3 permutation6
    mixedMoment B raw755step0 raw755step0Labels = mixedMoment B raw755step1 raw755step1Labels := by
      have ha : raw755step1 = -raw755step0 := by apply Matrix.ext; change ∀ i j, raw755step1 i j = -(raw755step0 i j); unfold raw755step1 raw755step0; decide +kernel
      have hl : raw755step1Labels = raw755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw755step1 raw755step1Labels = mixedMoment B raw755step2 raw755step2Labels := by
      have ha : raw755step2 = raw755step1 := by apply Matrix.ext; unfold raw755step2 raw755step1; decide +kernel
      have hl : raw755step1Labels = labelEmbedding1 ∘ raw755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw755step1 raw755step1Labels raw755step2Labels labelEmbedding1 hl
    _ = mixedMoment B node694 node694Labels := by rfl

def raw756 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw756step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw756 raw756Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw756 raw756Labels = mixedMoment B raw756step0 raw756step0Labels := by
      have ha : raw756step0 = (fun i j => raw756 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw756step0 raw756; decide +kernel
      have hl : raw756step0Labels = raw756Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw756 raw756Labels permutation152 permutation4
    mixedMoment B raw756step0 raw756step0Labels = mixedMoment B raw756step1 raw756step1Labels := by
      have ha : raw756step1 = raw756step0 := by apply Matrix.ext; unfold raw756step1 raw756step0; decide +kernel
      have hl : raw756step0Labels = labelEmbedding7 ∘ raw756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw756step0 raw756step0Labels raw756step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4139 node4139Labels := by rfl

def raw757 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw757 raw757Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw757 raw757Labels = mixedMoment B raw757step0 raw757step0Labels := by
      have ha : raw757step0 = (fun i j => raw757 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw757step0 raw757; decide +kernel
      have hl : raw757step0Labels = raw757Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw757 raw757Labels permutation152 permutation4
    _ = mixedMoment B node567 node567Labels := by rfl

def raw758 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw758Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw758step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw758step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw758step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw758 raw758Labels = mixedMoment B node1488 node1488Labels := by
  calc
    mixedMoment B raw758 raw758Labels = mixedMoment B raw758step0 raw758step0Labels := by
      have ha : raw758step0 = (fun i j => raw758 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw758step0 raw758; decide +kernel
      have hl : raw758step0Labels = raw758Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw758 raw758Labels permutation152 permutation6
    mixedMoment B raw758step0 raw758step0Labels = mixedMoment B raw758step1 raw758step1Labels := by
      have ha : raw758step1 = -raw758step0 := by apply Matrix.ext; change ∀ i j, raw758step1 i j = -(raw758step0 i j); unfold raw758step1 raw758step0; decide +kernel
      have hl : raw758step1Labels = raw758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw758step1 raw758step1Labels = mixedMoment B raw758step2 raw758step2Labels := by
      have ha : raw758step2 = raw758step1 := by apply Matrix.ext; unfold raw758step2 raw758step1; decide +kernel
      have hl : raw758step1Labels = labelEmbedding1 ∘ raw758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw758step1 raw758step1Labels raw758step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1488 node1488Labels := by rfl

def raw759 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw759step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw759 raw759Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw759 raw759Labels = mixedMoment B raw759step0 raw759step0Labels := by
      have ha : raw759step0 = (fun i j => raw759 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw759step0 raw759; decide +kernel
      have hl : raw759step0Labels = raw759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw759 raw759Labels permutation32 permutation4
    mixedMoment B raw759step0 raw759step0Labels = mixedMoment B raw759step1 raw759step1Labels := by
      have ha : raw759step1 = raw759step0 := by apply Matrix.ext; unfold raw759step1 raw759step0; decide +kernel
      have hl : raw759step0Labels = labelEmbedding7 ∘ raw759step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw759step0 raw759step0Labels raw759step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4140 node4140Labels := by rfl

def raw760 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw760 raw760Labels = mixedMoment B node568 node568Labels := by
  calc
    mixedMoment B raw760 raw760Labels = mixedMoment B raw760step0 raw760step0Labels := by
      have ha : raw760step0 = (fun i j => raw760 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw760step0 raw760; decide +kernel
      have hl : raw760step0Labels = raw760Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw760 raw760Labels permutation32 permutation4
    _ = mixedMoment B node568 node568Labels := by rfl

def raw761 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw761Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw761step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw761 raw761Labels = mixedMoment B node1489 node1489Labels := by
  calc
    mixedMoment B raw761 raw761Labels = mixedMoment B raw761step0 raw761step0Labels := by
      have ha : raw761step0 = (fun i j => raw761 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw761step0 raw761; decide +kernel
      have hl : raw761step0Labels = raw761Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw761 raw761Labels permutation32 permutation6
    mixedMoment B raw761step0 raw761step0Labels = mixedMoment B raw761step1 raw761step1Labels := by
      have ha : raw761step1 = -raw761step0 := by apply Matrix.ext; change ∀ i j, raw761step1 i j = -(raw761step0 i j); unfold raw761step1 raw761step0; decide +kernel
      have hl : raw761step1Labels = raw761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw761step1 raw761step1Labels = mixedMoment B raw761step2 raw761step2Labels := by
      have ha : raw761step2 = raw761step1 := by apply Matrix.ext; unfold raw761step2 raw761step1; decide +kernel
      have hl : raw761step1Labels = labelEmbedding1 ∘ raw761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw761step1 raw761step1Labels raw761step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1489 node1489Labels := by rfl

def raw762 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw762step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw762 raw762Labels = mixedMoment B node4141 node4141Labels := by
  calc
    mixedMoment B raw762 raw762Labels = mixedMoment B raw762step0 raw762step0Labels := by
      have ha : raw762step0 = (fun i j => raw762 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw762step0 raw762; decide +kernel
      have hl : raw762step0Labels = raw762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw762 raw762Labels permutation32 permutation4
    mixedMoment B raw762step0 raw762step0Labels = mixedMoment B raw762step1 raw762step1Labels := by
      have ha : raw762step1 = raw762step0 := by apply Matrix.ext; unfold raw762step1 raw762step0; decide +kernel
      have hl : raw762step0Labels = labelEmbedding7 ∘ raw762step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw762step0 raw762step0Labels raw762step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4141 node4141Labels := by rfl

def raw763 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw763 raw763Labels = mixedMoment B node569 node569Labels := by
  calc
    mixedMoment B raw763 raw763Labels = mixedMoment B raw763step0 raw763step0Labels := by
      have ha : raw763step0 = (fun i j => raw763 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw763step0 raw763; decide +kernel
      have hl : raw763step0Labels = raw763Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw763 raw763Labels permutation32 permutation4
    _ = mixedMoment B node569 node569Labels := by rfl

def raw764 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw764Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw764step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw764 raw764Labels = mixedMoment B node1490 node1490Labels := by
  calc
    mixedMoment B raw764 raw764Labels = mixedMoment B raw764step0 raw764step0Labels := by
      have ha : raw764step0 = (fun i j => raw764 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw764step0 raw764; decide +kernel
      have hl : raw764step0Labels = raw764Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw764 raw764Labels permutation32 permutation6
    mixedMoment B raw764step0 raw764step0Labels = mixedMoment B raw764step1 raw764step1Labels := by
      have ha : raw764step1 = -raw764step0 := by apply Matrix.ext; change ∀ i j, raw764step1 i j = -(raw764step0 i j); unfold raw764step1 raw764step0; decide +kernel
      have hl : raw764step1Labels = raw764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw764step1 raw764step1Labels = mixedMoment B raw764step2 raw764step2Labels := by
      have ha : raw764step2 = raw764step1 := by apply Matrix.ext; unfold raw764step2 raw764step1; decide +kernel
      have hl : raw764step1Labels = labelEmbedding1 ∘ raw764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw764step1 raw764step1Labels raw764step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1490 node1490Labels := by rfl

def raw765 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 4, -4]]
def raw765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw765step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw765step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw765 raw765Labels = mixedMoment B node4142 node4142Labels := by
  calc
    mixedMoment B raw765 raw765Labels = mixedMoment B raw765step0 raw765step0Labels := by
      have ha : raw765step0 = (fun i j => raw765 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw765step0 raw765; decide +kernel
      have hl : raw765step0Labels = raw765Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw765 raw765Labels permutation8 permutation4
    mixedMoment B raw765step0 raw765step0Labels = mixedMoment B raw765step1 raw765step1Labels := by
      have ha : raw765step1 = raw765step0 := by apply Matrix.ext; unfold raw765step1 raw765step0; decide +kernel
      have hl : raw765step0Labels = labelEmbedding7 ∘ raw765step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw765step0 raw765step0Labels raw765step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4142 node4142Labels := by rfl

def raw766 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 4, -4]]
def raw766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw766step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw766 raw766Labels = mixedMoment B node570 node570Labels := by
  calc
    mixedMoment B raw766 raw766Labels = mixedMoment B raw766step0 raw766step0Labels := by
      have ha : raw766step0 = (fun i j => raw766 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw766step0 raw766; decide +kernel
      have hl : raw766step0Labels = raw766Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw766 raw766Labels permutation8 permutation4
    _ = mixedMoment B node570 node570Labels := by rfl

def raw767 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 4, -4]]
def raw767Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw767step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw767step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw767 raw767Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw767 raw767Labels = mixedMoment B raw767step0 raw767step0Labels := by
      have ha : raw767step0 = (fun i j => raw767 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw767step0 raw767; decide +kernel
      have hl : raw767step0Labels = raw767Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw767 raw767Labels permutation31 permutation6
    mixedMoment B raw767step0 raw767step0Labels = mixedMoment B raw767step1 raw767step1Labels := by
      have ha : raw767step1 = raw767step0 := by apply Matrix.ext; unfold raw767step1 raw767step0; decide +kernel
      have hl : raw767step0Labels = labelEmbedding1 ∘ raw767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw767step0 raw767step0Labels raw767step1Labels labelEmbedding1 hl
    _ = mixedMoment B node765 node765Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
