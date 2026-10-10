import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25472 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25472step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25472 raw25472Labels = mixedMoment B node4406 node4406Labels := by
  calc
    mixedMoment B raw25472 raw25472Labels = mixedMoment B raw25472step0 raw25472step0Labels := by
      have ha : raw25472step0 = (fun i j => raw25472 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25472step0 raw25472; decide +kernel
      have hl : raw25472step0Labels = raw25472Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25472 raw25472Labels permutation176 permutation6
    mixedMoment B raw25472step0 raw25472step0Labels = mixedMoment B raw25472step1 raw25472step1Labels := by
      have ha : raw25472step1 = raw25472step0 := by apply Matrix.ext; unfold raw25472step1 raw25472step0; decide +kernel
      have hl : raw25472step0Labels = labelEmbedding9 ∘ raw25472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25472step0 raw25472step0Labels raw25472step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4406 node4406Labels := by rfl

def raw25473 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25473step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25473 raw25473Labels = mixedMoment B node4470 node4470Labels := by
  calc
    mixedMoment B raw25473 raw25473Labels = mixedMoment B raw25473step0 raw25473step0Labels := by
      have hz : ∀ j, raw25473 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25473step0 = (fun i j => raw25473 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25473step0 raw25473; decide +kernel
      have hl : raw25473step0Labels = raw25473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25473 raw25473Labels permutation346 hz
    mixedMoment B raw25473step0 raw25473step0Labels = mixedMoment B raw25473step1 raw25473step1Labels := by
      have ha : raw25473step1 = (fun i j => raw25473step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25473step1 raw25473step0; decide +kernel
      have hl : raw25473step1Labels = raw25473step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25473step0 raw25473step0Labels permutation32 permutation6
    mixedMoment B raw25473step1 raw25473step1Labels = mixedMoment B raw25473step2 raw25473step2Labels := by
      have ha : raw25473step2 = raw25473step1 := by apply Matrix.ext; unfold raw25473step2 raw25473step1; decide +kernel
      have hl : raw25473step1Labels = labelEmbedding9 ∘ raw25473step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25473step1 raw25473step1Labels raw25473step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4470 node4470Labels := by rfl

def raw25474 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25474step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25474 raw25474Labels = mixedMoment B node4470 node4470Labels := by
  calc
    mixedMoment B raw25474 raw25474Labels = mixedMoment B raw25474step0 raw25474step0Labels := by
      have hz : ∀ j, raw25474 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25474step0 = (fun i j => raw25474 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25474step0 raw25474; decide +kernel
      have hl : raw25474step0Labels = raw25474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25474 raw25474Labels permutation346 hz
    mixedMoment B raw25474step0 raw25474step0Labels = mixedMoment B raw25474step1 raw25474step1Labels := by
      have ha : raw25474step1 = (fun i j => raw25474step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25474step1 raw25474step0; decide +kernel
      have hl : raw25474step1Labels = raw25474step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25474step0 raw25474step0Labels permutation34 permutation6
    mixedMoment B raw25474step1 raw25474step1Labels = mixedMoment B raw25474step2 raw25474step2Labels := by
      have ha : raw25474step2 = raw25474step1 := by apply Matrix.ext; unfold raw25474step2 raw25474step1; decide +kernel
      have hl : raw25474step1Labels = labelEmbedding9 ∘ raw25474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25474step1 raw25474step1Labels raw25474step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4470 node4470Labels := by rfl

def raw25475 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw25475step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25475step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25475step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25475step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25475 raw25475Labels = mixedMoment B node4248 node4248Labels := by
  calc
    mixedMoment B raw25475 raw25475Labels = mixedMoment B raw25475step0 raw25475step0Labels := by
      have ha : raw25475step0 = (fun i j => raw25475 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25475step0 raw25475; decide +kernel
      have hl : raw25475step0Labels = raw25475Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25475 raw25475Labels permutation212 permutation4
    mixedMoment B raw25475step0 raw25475step0Labels = mixedMoment B raw25475step1 raw25475step1Labels := by
      have ha : raw25475step1 = -raw25475step0 := by apply Matrix.ext; change ∀ i j, raw25475step1 i j = -(raw25475step0 i j); unfold raw25475step1 raw25475step0; decide +kernel
      have hl : raw25475step1Labels = raw25475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25475step1 raw25475step1Labels = mixedMoment B raw25475step2 raw25475step2Labels := by
      have ha : raw25475step2 = raw25475step1 := by apply Matrix.ext; unfold raw25475step2 raw25475step1; decide +kernel
      have hl : raw25475step1Labels = labelEmbedding7 ∘ raw25475step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25475step1 raw25475step1Labels raw25475step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4248 node4248Labels := by rfl

def raw25476 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25476step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25476 raw25476Labels = mixedMoment B node4435 node4435Labels := by
  calc
    mixedMoment B raw25476 raw25476Labels = mixedMoment B raw25476step0 raw25476step0Labels := by
      have ha : raw25476step0 = (fun i j => raw25476 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25476step0 raw25476; decide +kernel
      have hl : raw25476step0Labels = raw25476Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25476 raw25476Labels permutation152 permutation6
    mixedMoment B raw25476step0 raw25476step0Labels = mixedMoment B raw25476step1 raw25476step1Labels := by
      have ha : raw25476step1 = raw25476step0 := by apply Matrix.ext; unfold raw25476step1 raw25476step0; decide +kernel
      have hl : raw25476step0Labels = labelEmbedding9 ∘ raw25476step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25476step0 raw25476step0Labels raw25476step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4435 node4435Labels := by rfl

def raw25477 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25477step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25477 raw25477Labels = mixedMoment B node4435 node4435Labels := by
  calc
    mixedMoment B raw25477 raw25477Labels = mixedMoment B raw25477step0 raw25477step0Labels := by
      have ha : raw25477step0 = (fun i j => raw25477 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25477step0 raw25477; decide +kernel
      have hl : raw25477step0Labels = raw25477Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25477 raw25477Labels permutation154 permutation6
    mixedMoment B raw25477step0 raw25477step0Labels = mixedMoment B raw25477step1 raw25477step1Labels := by
      have ha : raw25477step1 = raw25477step0 := by apply Matrix.ext; unfold raw25477step1 raw25477step0; decide +kernel
      have hl : raw25477step0Labels = labelEmbedding9 ∘ raw25477step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25477step0 raw25477step0Labels raw25477step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4435 node4435Labels := by rfl

def raw25478 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25478step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25478step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25478step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25478step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25478 raw25478Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw25478 raw25478Labels = mixedMoment B raw25478step0 raw25478step0Labels := by
      have hz : ∀ j, raw25478 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25478step0 = (fun i j => raw25478 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25478step0 raw25478; decide +kernel
      have hl : raw25478step0Labels = raw25478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25478 raw25478Labels permutation346 hz
    mixedMoment B raw25478step0 raw25478step0Labels = mixedMoment B raw25478step1 raw25478step1Labels := by
      have ha : raw25478step1 = (fun i j => raw25478step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25478step1 raw25478step0; decide +kernel
      have hl : raw25478step1Labels = raw25478step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25478step0 raw25478step0Labels permutation38 permutation4
    mixedMoment B raw25478step1 raw25478step1Labels = mixedMoment B raw25478step2 raw25478step2Labels := by
      have ha : raw25478step2 = -raw25478step1 := by apply Matrix.ext; change ∀ i j, raw25478step2 i j = -(raw25478step1 i j); unfold raw25478step2 raw25478step1; decide +kernel
      have hl : raw25478step2Labels = raw25478step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25478step2 raw25478step2Labels = mixedMoment B raw25478step3 raw25478step3Labels := by
      have ha : raw25478step3 = raw25478step2 := by apply Matrix.ext; unfold raw25478step3 raw25478step2; decide +kernel
      have hl : raw25478step2Labels = labelEmbedding7 ∘ raw25478step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25478step2 raw25478step2Labels raw25478step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4264 node4264Labels := by rfl

def raw25479 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25479step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25479 raw25479Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw25479 raw25479Labels = mixedMoment B raw25479step0 raw25479step0Labels := by
      have ha : raw25479step0 = (fun i j => raw25479 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25479step0 raw25479; decide +kernel
      have hl : raw25479step0Labels = raw25479Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25479 raw25479Labels permutation176 permutation6
    mixedMoment B raw25479step0 raw25479step0Labels = mixedMoment B raw25479step1 raw25479step1Labels := by
      have ha : raw25479step1 = raw25479step0 := by apply Matrix.ext; unfold raw25479step1 raw25479step0; decide +kernel
      have hl : raw25479step0Labels = labelEmbedding9 ∘ raw25479step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25479step0 raw25479step0Labels raw25479step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw25480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25480step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25480step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25480 raw25480Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw25480 raw25480Labels = mixedMoment B raw25480step0 raw25480step0Labels := by
      have hz : ∀ j, raw25480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25480step0 = (fun i j => raw25480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25480step0 raw25480; decide +kernel
      have hl : raw25480step0Labels = raw25480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25480 raw25480Labels permutation346 hz
    mixedMoment B raw25480step0 raw25480step0Labels = mixedMoment B raw25480step1 raw25480step1Labels := by
      have ha : raw25480step1 = (fun i j => raw25480step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25480step1 raw25480step0; decide +kernel
      have hl : raw25480step1Labels = raw25480step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25480step0 raw25480step0Labels permutation32 permutation6
    mixedMoment B raw25480step1 raw25480step1Labels = mixedMoment B raw25480step2 raw25480step2Labels := by
      have ha : raw25480step2 = raw25480step1 := by apply Matrix.ext; unfold raw25480step2 raw25480step1; decide +kernel
      have hl : raw25480step1Labels = labelEmbedding9 ∘ raw25480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25480step1 raw25480step1Labels raw25480step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw25481 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw25481step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25481step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25481step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25481step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25481 raw25481Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw25481 raw25481Labels = mixedMoment B raw25481step0 raw25481step0Labels := by
      have hz : ∀ j, raw25481 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25481step0 = (fun i j => raw25481 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25481step0 raw25481; decide +kernel
      have hl : raw25481step0Labels = raw25481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25481 raw25481Labels permutation346 hz
    mixedMoment B raw25481step0 raw25481step0Labels = mixedMoment B raw25481step1 raw25481step1Labels := by
      have ha : raw25481step1 = (fun i j => raw25481step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25481step1 raw25481step0; decide +kernel
      have hl : raw25481step1Labels = raw25481step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25481step0 raw25481step0Labels permutation40 permutation4
    mixedMoment B raw25481step1 raw25481step1Labels = mixedMoment B raw25481step2 raw25481step2Labels := by
      have ha : raw25481step2 = -raw25481step1 := by apply Matrix.ext; change ∀ i j, raw25481step2 i j = -(raw25481step1 i j); unfold raw25481step2 raw25481step1; decide +kernel
      have hl : raw25481step2Labels = raw25481step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25481step2 raw25481step2Labels = mixedMoment B raw25481step3 raw25481step3Labels := by
      have ha : raw25481step3 = raw25481step2 := by apply Matrix.ext; unfold raw25481step3 raw25481step2; decide +kernel
      have hl : raw25481step2Labels = labelEmbedding7 ∘ raw25481step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25481step2 raw25481step2Labels raw25481step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw25482 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25482step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25482 raw25482Labels = mixedMoment B node4395 node4395Labels := by
  calc
    mixedMoment B raw25482 raw25482Labels = mixedMoment B raw25482step0 raw25482step0Labels := by
      have ha : raw25482step0 = (fun i j => raw25482 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25482step0 raw25482; decide +kernel
      have hl : raw25482step0Labels = raw25482Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25482 raw25482Labels permutation176 permutation6
    mixedMoment B raw25482step0 raw25482step0Labels = mixedMoment B raw25482step1 raw25482step1Labels := by
      have ha : raw25482step1 = raw25482step0 := by apply Matrix.ext; unfold raw25482step1 raw25482step0; decide +kernel
      have hl : raw25482step0Labels = labelEmbedding9 ∘ raw25482step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25482step0 raw25482step0Labels raw25482step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4395 node4395Labels := by rfl

def raw25483 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25483step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25483 raw25483Labels = mixedMoment B node4450 node4450Labels := by
  calc
    mixedMoment B raw25483 raw25483Labels = mixedMoment B raw25483step0 raw25483step0Labels := by
      have hz : ∀ j, raw25483 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25483step0 = (fun i j => raw25483 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25483step0 raw25483; decide +kernel
      have hl : raw25483step0Labels = raw25483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25483 raw25483Labels permutation346 hz
    mixedMoment B raw25483step0 raw25483step0Labels = mixedMoment B raw25483step1 raw25483step1Labels := by
      have ha : raw25483step1 = (fun i j => raw25483step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25483step1 raw25483step0; decide +kernel
      have hl : raw25483step1Labels = raw25483step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25483step0 raw25483step0Labels permutation32 permutation6
    mixedMoment B raw25483step1 raw25483step1Labels = mixedMoment B raw25483step2 raw25483step2Labels := by
      have ha : raw25483step2 = raw25483step1 := by apply Matrix.ext; unfold raw25483step2 raw25483step1; decide +kernel
      have hl : raw25483step1Labels = labelEmbedding9 ∘ raw25483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25483step1 raw25483step1Labels raw25483step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4450 node4450Labels := by rfl

def raw25484 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25484step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25484 raw25484Labels = mixedMoment B node4450 node4450Labels := by
  calc
    mixedMoment B raw25484 raw25484Labels = mixedMoment B raw25484step0 raw25484step0Labels := by
      have hz : ∀ j, raw25484 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25484step0 = (fun i j => raw25484 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25484step0 raw25484; decide +kernel
      have hl : raw25484step0Labels = raw25484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25484 raw25484Labels permutation346 hz
    mixedMoment B raw25484step0 raw25484step0Labels = mixedMoment B raw25484step1 raw25484step1Labels := by
      have ha : raw25484step1 = (fun i j => raw25484step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25484step1 raw25484step0; decide +kernel
      have hl : raw25484step1Labels = raw25484step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25484step0 raw25484step0Labels permutation34 permutation6
    mixedMoment B raw25484step1 raw25484step1Labels = mixedMoment B raw25484step2 raw25484step2Labels := by
      have ha : raw25484step2 = raw25484step1 := by apply Matrix.ext; unfold raw25484step2 raw25484step1; decide +kernel
      have hl : raw25484step1Labels = labelEmbedding9 ∘ raw25484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25484step1 raw25484step1Labels raw25484step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4450 node4450Labels := by rfl

def raw25485 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25485Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25485step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25485step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25485step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25485step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25485step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25485step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25485 raw25485Labels = mixedMoment B node1305 node1305Labels := by
  calc
    mixedMoment B raw25485 raw25485Labels = mixedMoment B raw25485step0 raw25485step0Labels := by
      have hz : ∀ j, raw25485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25485step0 = (fun i j => raw25485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25485step0 raw25485; decide +kernel
      have hl : raw25485step0Labels = raw25485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25485 raw25485Labels permutation346 hz
    mixedMoment B raw25485step0 raw25485step0Labels = mixedMoment B raw25485step1 raw25485step1Labels := by
      have hz : ∀ j, raw25485step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25485step1 = (fun i j => raw25485step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25485step1 raw25485step0; decide +kernel
      have hl : raw25485step1Labels = raw25485step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25485step0 raw25485step0Labels permutation56 hz
    mixedMoment B raw25485step1 raw25485step1Labels = mixedMoment B raw25485step2 raw25485step2Labels := by
      have ha : raw25485step2 = (fun i j => raw25485step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25485step2 raw25485step1; decide +kernel
      have hl : raw25485step2Labels = raw25485step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25485step1 raw25485step1Labels permutation8 permutation7
    mixedMoment B raw25485step2 raw25485step2Labels = mixedMoment B raw25485step3 raw25485step3Labels := by
      have ha : raw25485step3 = raw25485step2 := by apply Matrix.ext; unfold raw25485step3 raw25485step2; decide +kernel
      have hl : raw25485step2Labels = labelEmbedding1 ∘ raw25485step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25485step2 raw25485step2Labels raw25485step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1305 node1305Labels := by rfl

def raw25486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25486Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25486step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25486step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25486 raw25486Labels = mixedMoment B node1470 node1470Labels := by
  calc
    mixedMoment B raw25486 raw25486Labels = mixedMoment B raw25486step0 raw25486step0Labels := by
      have hz : ∀ j, raw25486 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25486step0 = (fun i j => raw25486 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25486step0 raw25486; decide +kernel
      have hl : raw25486step0Labels = raw25486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25486 raw25486Labels permutation346 hz
    mixedMoment B raw25486step0 raw25486step0Labels = mixedMoment B raw25486step1 raw25486step1Labels := by
      have ha : raw25486step1 = (fun i j => raw25486step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25486step1 raw25486step0; decide +kernel
      have hl : raw25486step1Labels = raw25486step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25486step0 raw25486step0Labels permutation32 permutation7
    mixedMoment B raw25486step1 raw25486step1Labels = mixedMoment B raw25486step2 raw25486step2Labels := by
      have ha : raw25486step2 = raw25486step1 := by apply Matrix.ext; unfold raw25486step2 raw25486step1; decide +kernel
      have hl : raw25486step1Labels = labelEmbedding1 ∘ raw25486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25486step1 raw25486step1Labels raw25486step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1470 node1470Labels := by rfl

def raw25487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25487Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25487step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25487step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25487 raw25487Labels = mixedMoment B node1360 node1360Labels := by
  calc
    mixedMoment B raw25487 raw25487Labels = mixedMoment B raw25487step0 raw25487step0Labels := by
      have ha : raw25487step0 = (fun i j => raw25487 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25487step0 raw25487; decide +kernel
      have hl : raw25487step0Labels = raw25487Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25487 raw25487Labels permutation152 permutation7
    mixedMoment B raw25487step0 raw25487step0Labels = mixedMoment B raw25487step1 raw25487step1Labels := by
      have ha : raw25487step1 = raw25487step0 := by apply Matrix.ext; unfold raw25487step1 raw25487step0; decide +kernel
      have hl : raw25487step0Labels = labelEmbedding1 ∘ raw25487step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25487step0 raw25487step0Labels raw25487step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1360 node1360Labels := by rfl

def raw25488 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25488Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25488step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25488step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25488 raw25488Labels = mixedMoment B node1371 node1371Labels := by
  calc
    mixedMoment B raw25488 raw25488Labels = mixedMoment B raw25488step0 raw25488step0Labels := by
      have hz : ∀ j, raw25488 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25488step0 = (fun i j => raw25488 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25488step0 raw25488; decide +kernel
      have hl : raw25488step0Labels = raw25488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25488 raw25488Labels permutation346 hz
    mixedMoment B raw25488step0 raw25488step0Labels = mixedMoment B raw25488step1 raw25488step1Labels := by
      have ha : raw25488step1 = (fun i j => raw25488step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25488step1 raw25488step0; decide +kernel
      have hl : raw25488step1Labels = raw25488step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25488step0 raw25488step0Labels permutation34 permutation7
    mixedMoment B raw25488step1 raw25488step1Labels = mixedMoment B raw25488step2 raw25488step2Labels := by
      have ha : raw25488step2 = raw25488step1 := by apply Matrix.ext; unfold raw25488step2 raw25488step1; decide +kernel
      have hl : raw25488step1Labels = labelEmbedding1 ∘ raw25488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25488step1 raw25488step1Labels raw25488step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1371 node1371Labels := by rfl

def raw25489 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25489Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25489step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25489 raw25489Labels = mixedMoment B node1371 node1371Labels := by
  calc
    mixedMoment B raw25489 raw25489Labels = mixedMoment B raw25489step0 raw25489step0Labels := by
      have hz : ∀ j, raw25489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25489step0 = (fun i j => raw25489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25489step0 raw25489; decide +kernel
      have hl : raw25489step0Labels = raw25489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25489 raw25489Labels permutation346 hz
    mixedMoment B raw25489step0 raw25489step0Labels = mixedMoment B raw25489step1 raw25489step1Labels := by
      have ha : raw25489step1 = (fun i j => raw25489step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25489step1 raw25489step0; decide +kernel
      have hl : raw25489step1Labels = raw25489step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25489step0 raw25489step0Labels permutation32 permutation7
    mixedMoment B raw25489step1 raw25489step1Labels = mixedMoment B raw25489step2 raw25489step2Labels := by
      have ha : raw25489step2 = raw25489step1 := by apply Matrix.ext; unfold raw25489step2 raw25489step1; decide +kernel
      have hl : raw25489step1Labels = labelEmbedding1 ∘ raw25489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25489step1 raw25489step1Labels raw25489step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1371 node1371Labels := by rfl

def raw25490 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25490Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw25490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25490 raw25490Labels = mixedMoment B node1477 node1477Labels := by
  calc
    mixedMoment B raw25490 raw25490Labels = mixedMoment B raw25490step0 raw25490step0Labels := by
      have ha : raw25490step0 = (fun i j => raw25490 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw25490step0 raw25490; decide +kernel
      have hl : raw25490step0Labels = raw25490Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25490 raw25490Labels permutation212 permutation5
    mixedMoment B raw25490step0 raw25490step0Labels = mixedMoment B raw25490step1 raw25490step1Labels := by
      have ha : raw25490step1 = -raw25490step0 := by apply Matrix.ext; change ∀ i j, raw25490step1 i j = -(raw25490step0 i j); unfold raw25490step1 raw25490step0; decide +kernel
      have hl : raw25490step1Labels = raw25490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25490step1 raw25490step1Labels = mixedMoment B raw25490step2 raw25490step2Labels := by
      have ha : raw25490step2 = raw25490step1 := by apply Matrix.ext; unfold raw25490step2 raw25490step1; decide +kernel
      have hl : raw25490step1Labels = labelEmbedding1 ∘ raw25490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25490step1 raw25490step1Labels raw25490step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1477 node1477Labels := by rfl

def raw25491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25491step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25491 raw25491Labels = mixedMoment B node1387 node1387Labels := by
  calc
    mixedMoment B raw25491 raw25491Labels = mixedMoment B raw25491step0 raw25491step0Labels := by
      have ha : raw25491step0 = (fun i j => raw25491 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25491step0 raw25491; decide +kernel
      have hl : raw25491step0Labels = raw25491Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25491 raw25491Labels permutation154 permutation7
    mixedMoment B raw25491step0 raw25491step0Labels = mixedMoment B raw25491step1 raw25491step1Labels := by
      have ha : raw25491step1 = raw25491step0 := by apply Matrix.ext; unfold raw25491step1 raw25491step0; decide +kernel
      have hl : raw25491step0Labels = labelEmbedding1 ∘ raw25491step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25491step0 raw25491step0Labels raw25491step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1387 node1387Labels := by rfl

def raw25492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25492 raw25492Labels = mixedMoment B node1387 node1387Labels := by
  calc
    mixedMoment B raw25492 raw25492Labels = mixedMoment B raw25492step0 raw25492step0Labels := by
      have ha : raw25492step0 = (fun i j => raw25492 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25492step0 raw25492; decide +kernel
      have hl : raw25492step0Labels = raw25492Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25492 raw25492Labels permutation152 permutation7
    mixedMoment B raw25492step0 raw25492step0Labels = mixedMoment B raw25492step1 raw25492step1Labels := by
      have ha : raw25492step1 = raw25492step0 := by apply Matrix.ext; unfold raw25492step1 raw25492step0; decide +kernel
      have hl : raw25492step0Labels = labelEmbedding1 ∘ raw25492step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25492step0 raw25492step0Labels raw25492step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1387 node1387Labels := by rfl

def raw25493 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25493Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25493step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25493step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25493 raw25493Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw25493 raw25493Labels = mixedMoment B raw25493step0 raw25493step0Labels := by
      have hz : ∀ j, raw25493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25493step0 = (fun i j => raw25493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25493step0 raw25493; decide +kernel
      have hl : raw25493step0Labels = raw25493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25493 raw25493Labels permutation346 hz
    mixedMoment B raw25493step0 raw25493step0Labels = mixedMoment B raw25493step1 raw25493step1Labels := by
      have ha : raw25493step1 = (fun i j => raw25493step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25493step1 raw25493step0; decide +kernel
      have hl : raw25493step1Labels = raw25493step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25493step0 raw25493step0Labels permutation32 permutation7
    mixedMoment B raw25493step1 raw25493step1Labels = mixedMoment B raw25493step2 raw25493step2Labels := by
      have ha : raw25493step2 = raw25493step1 := by apply Matrix.ext; unfold raw25493step2 raw25493step1; decide +kernel
      have hl : raw25493step1Labels = labelEmbedding1 ∘ raw25493step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25493step1 raw25493step1Labels raw25493step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw25494 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25494step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw25494step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25494step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25494step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25494step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25494step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25494 raw25494Labels = mixedMoment B node1483 node1483Labels := by
  calc
    mixedMoment B raw25494 raw25494Labels = mixedMoment B raw25494step0 raw25494step0Labels := by
      have hz : ∀ j, raw25494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25494step0 = (fun i j => raw25494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25494step0 raw25494; decide +kernel
      have hl : raw25494step0Labels = raw25494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25494 raw25494Labels permutation346 hz
    mixedMoment B raw25494step0 raw25494step0Labels = mixedMoment B raw25494step1 raw25494step1Labels := by
      have ha : raw25494step1 = (fun i j => raw25494step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw25494step1 raw25494step0; decide +kernel
      have hl : raw25494step1Labels = raw25494step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25494step0 raw25494step0Labels permutation40 permutation5
    mixedMoment B raw25494step1 raw25494step1Labels = mixedMoment B raw25494step2 raw25494step2Labels := by
      have ha : raw25494step2 = -raw25494step1 := by apply Matrix.ext; change ∀ i j, raw25494step2 i j = -(raw25494step1 i j); unfold raw25494step2 raw25494step1; decide +kernel
      have hl : raw25494step2Labels = raw25494step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25494step2 raw25494step2Labels = mixedMoment B raw25494step3 raw25494step3Labels := by
      have ha : raw25494step3 = raw25494step2 := by apply Matrix.ext; unfold raw25494step3 raw25494step2; decide +kernel
      have hl : raw25494step2Labels = labelEmbedding1 ∘ raw25494step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25494step2 raw25494step2Labels raw25494step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1483 node1483Labels := by rfl

def raw25495 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25495step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25495 raw25495Labels = mixedMoment B node1396 node1396Labels := by
  calc
    mixedMoment B raw25495 raw25495Labels = mixedMoment B raw25495step0 raw25495step0Labels := by
      have ha : raw25495step0 = (fun i j => raw25495 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25495step0 raw25495; decide +kernel
      have hl : raw25495step0Labels = raw25495Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25495 raw25495Labels permutation154 permutation7
    mixedMoment B raw25495step0 raw25495step0Labels = mixedMoment B raw25495step1 raw25495step1Labels := by
      have ha : raw25495step1 = raw25495step0 := by apply Matrix.ext; unfold raw25495step1 raw25495step0; decide +kernel
      have hl : raw25495step0Labels = labelEmbedding1 ∘ raw25495step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25495step0 raw25495step0Labels raw25495step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1396 node1396Labels := by rfl

def raw25496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25496step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25496 raw25496Labels = mixedMoment B node1412 node1412Labels := by
  calc
    mixedMoment B raw25496 raw25496Labels = mixedMoment B raw25496step0 raw25496step0Labels := by
      have hz : ∀ j, raw25496 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25496step0 = (fun i j => raw25496 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25496step0 raw25496; decide +kernel
      have hl : raw25496step0Labels = raw25496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25496 raw25496Labels permutation346 hz
    mixedMoment B raw25496step0 raw25496step0Labels = mixedMoment B raw25496step1 raw25496step1Labels := by
      have ha : raw25496step1 = (fun i j => raw25496step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25496step1 raw25496step0; decide +kernel
      have hl : raw25496step1Labels = raw25496step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25496step0 raw25496step0Labels permutation34 permutation7
    mixedMoment B raw25496step1 raw25496step1Labels = mixedMoment B raw25496step2 raw25496step2Labels := by
      have ha : raw25496step2 = raw25496step1 := by apply Matrix.ext; unfold raw25496step2 raw25496step1; decide +kernel
      have hl : raw25496step1Labels = labelEmbedding1 ∘ raw25496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25496step1 raw25496step1Labels raw25496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1412 node1412Labels := by rfl

def raw25497 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25497step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw25497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25497step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25497step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25497step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25497 raw25497Labels = mixedMoment B node1478 node1478Labels := by
  calc
    mixedMoment B raw25497 raw25497Labels = mixedMoment B raw25497step0 raw25497step0Labels := by
      have hz : ∀ j, raw25497 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25497step0 = (fun i j => raw25497 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25497step0 raw25497; decide +kernel
      have hl : raw25497step0Labels = raw25497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25497 raw25497Labels permutation346 hz
    mixedMoment B raw25497step0 raw25497step0Labels = mixedMoment B raw25497step1 raw25497step1Labels := by
      have ha : raw25497step1 = (fun i j => raw25497step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw25497step1 raw25497step0; decide +kernel
      have hl : raw25497step1Labels = raw25497step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25497step0 raw25497step0Labels permutation40 permutation5
    mixedMoment B raw25497step1 raw25497step1Labels = mixedMoment B raw25497step2 raw25497step2Labels := by
      have ha : raw25497step2 = -raw25497step1 := by apply Matrix.ext; change ∀ i j, raw25497step2 i j = -(raw25497step1 i j); unfold raw25497step2 raw25497step1; decide +kernel
      have hl : raw25497step2Labels = raw25497step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25497step2 raw25497step2Labels = mixedMoment B raw25497step3 raw25497step3Labels := by
      have ha : raw25497step3 = raw25497step2 := by apply Matrix.ext; unfold raw25497step3 raw25497step2; decide +kernel
      have hl : raw25497step2Labels = labelEmbedding1 ∘ raw25497step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25497step2 raw25497step2Labels raw25497step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1478 node1478Labels := by rfl

def raw25498 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25498 raw25498Labels = mixedMoment B node1398 node1398Labels := by
  calc
    mixedMoment B raw25498 raw25498Labels = mixedMoment B raw25498step0 raw25498step0Labels := by
      have ha : raw25498step0 = (fun i j => raw25498 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25498step0 raw25498; decide +kernel
      have hl : raw25498step0Labels = raw25498Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25498 raw25498Labels permutation152 permutation7
    mixedMoment B raw25498step0 raw25498step0Labels = mixedMoment B raw25498step1 raw25498step1Labels := by
      have ha : raw25498step1 = raw25498step0 := by apply Matrix.ext; unfold raw25498step1 raw25498step0; decide +kernel
      have hl : raw25498step0Labels = labelEmbedding1 ∘ raw25498step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25498step0 raw25498step0Labels raw25498step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1398 node1398Labels := by rfl

def raw25499 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25499 raw25499Labels = mixedMoment B node1415 node1415Labels := by
  calc
    mixedMoment B raw25499 raw25499Labels = mixedMoment B raw25499step0 raw25499step0Labels := by
      have hz : ∀ j, raw25499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25499step0 = (fun i j => raw25499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25499step0 raw25499; decide +kernel
      have hl : raw25499step0Labels = raw25499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25499 raw25499Labels permutation346 hz
    mixedMoment B raw25499step0 raw25499step0Labels = mixedMoment B raw25499step1 raw25499step1Labels := by
      have ha : raw25499step1 = (fun i j => raw25499step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25499step1 raw25499step0; decide +kernel
      have hl : raw25499step1Labels = raw25499step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25499step0 raw25499step0Labels permutation34 permutation7
    mixedMoment B raw25499step1 raw25499step1Labels = mixedMoment B raw25499step2 raw25499step2Labels := by
      have ha : raw25499step2 = raw25499step1 := by apply Matrix.ext; unfold raw25499step2 raw25499step1; decide +kernel
      have hl : raw25499step1Labels = labelEmbedding1 ∘ raw25499step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25499step1 raw25499step1Labels raw25499step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1415 node1415Labels := by rfl

def raw25500 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25500 raw25500Labels = mixedMoment B node1415 node1415Labels := by
  calc
    mixedMoment B raw25500 raw25500Labels = mixedMoment B raw25500step0 raw25500step0Labels := by
      have hz : ∀ j, raw25500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25500step0 = (fun i j => raw25500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25500step0 raw25500; decide +kernel
      have hl : raw25500step0Labels = raw25500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25500 raw25500Labels permutation346 hz
    mixedMoment B raw25500step0 raw25500step0Labels = mixedMoment B raw25500step1 raw25500step1Labels := by
      have ha : raw25500step1 = (fun i j => raw25500step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25500step1 raw25500step0; decide +kernel
      have hl : raw25500step1Labels = raw25500step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25500step0 raw25500step0Labels permutation32 permutation7
    mixedMoment B raw25500step1 raw25500step1Labels = mixedMoment B raw25500step2 raw25500step2Labels := by
      have ha : raw25500step2 = raw25500step1 := by apply Matrix.ext; unfold raw25500step2 raw25500step1; decide +kernel
      have hl : raw25500step1Labels = labelEmbedding1 ∘ raw25500step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25500step1 raw25500step1Labels raw25500step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1415 node1415Labels := by rfl

def raw25501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw25501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw25501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25501 raw25501Labels = mixedMoment B node2099 node2099Labels := by
  calc
    mixedMoment B raw25501 raw25501Labels = mixedMoment B raw25501step0 raw25501step0Labels := by
      have hz : ∀ j, raw25501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25501step0 = (fun i j => raw25501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25501step0 raw25501; decide +kernel
      have hl : raw25501step0Labels = raw25501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25501 raw25501Labels permutation346 hz
    mixedMoment B raw25501step0 raw25501step0Labels = mixedMoment B raw25501step1 raw25501step1Labels := by
      have ha : raw25501step1 = (fun i j => raw25501step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25501step1 raw25501step0; decide +kernel
      have hl : raw25501step1Labels = raw25501step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25501step0 raw25501step0Labels permutation34 permutation2
    _ = mixedMoment B node2099 node2099Labels := by rfl

def raw25502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw25502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25502 raw25502Labels = mixedMoment B node2015 node2015Labels := by
  calc
    mixedMoment B raw25502 raw25502Labels = mixedMoment B raw25502step0 raw25502step0Labels := by
      have ha : raw25502step0 = (fun i j => raw25502 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25502step0 raw25502; decide +kernel
      have hl : raw25502step0Labels = raw25502Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25502 raw25502Labels permutation178 permutation2
    _ = mixedMoment B node2015 node2015Labels := by rfl

def raw25503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw25503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw25503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25503 raw25503Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw25503 raw25503Labels = mixedMoment B raw25503step0 raw25503step0Labels := by
      have hz : ∀ j, raw25503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25503step0 = (fun i j => raw25503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25503step0 raw25503; decide +kernel
      have hl : raw25503step0Labels = raw25503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25503 raw25503Labels permutation346 hz
    mixedMoment B raw25503step0 raw25503step0Labels = mixedMoment B raw25503step1 raw25503step1Labels := by
      have ha : raw25503step1 = (fun i j => raw25503step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25503step1 raw25503step0; decide +kernel
      have hl : raw25503step1Labels = raw25503step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25503step0 raw25503step0Labels permutation44 permutation2
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw25504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw25504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw25504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw25504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25504 raw25504Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw25504 raw25504Labels = mixedMoment B raw25504step0 raw25504step0Labels := by
      have hz : ∀ j, raw25504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25504step0 = (fun i j => raw25504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25504step0 raw25504; decide +kernel
      have hl : raw25504step0Labels = raw25504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25504 raw25504Labels permutation346 hz
    mixedMoment B raw25504step0 raw25504step0Labels = mixedMoment B raw25504step1 raw25504step1Labels := by
      have ha : raw25504step1 = (fun i j => raw25504step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25504step1 raw25504step0; decide +kernel
      have hl : raw25504step1Labels = raw25504step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25504step0 raw25504step0Labels permutation34 permutation2
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw25505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25505 raw25505Labels = mixedMoment B node981 node981Labels := by
  calc
    mixedMoment B raw25505 raw25505Labels = mixedMoment B raw25505step0 raw25505step0Labels := by
      have ha : raw25505step0 = (fun i j => raw25505 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25505step0 raw25505; decide +kernel
      have hl : raw25505step0Labels = raw25505Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25505 raw25505Labels permutation178 permutation2
    _ = mixedMoment B node981 node981Labels := by rfl

def raw25506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25506 raw25506Labels = mixedMoment B node2078 node2078Labels := by
  calc
    mixedMoment B raw25506 raw25506Labels = mixedMoment B raw25506step0 raw25506step0Labels := by
      have ha : raw25506step0 = (fun i j => raw25506 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25506step0 raw25506; decide +kernel
      have hl : raw25506step0Labels = raw25506Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25506 raw25506Labels permutation154 permutation2
    _ = mixedMoment B node2078 node2078Labels := by rfl

def raw25507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25507 raw25507Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw25507 raw25507Labels = mixedMoment B raw25507step0 raw25507step0Labels := by
      have ha : raw25507step0 = (fun i j => raw25507 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25507step0 raw25507; decide +kernel
      have hl : raw25507step0Labels = raw25507Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25507 raw25507Labels permutation178 permutation2
    _ = mixedMoment B node1913 node1913Labels := by rfl

def raw25508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25508 raw25508Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw25508 raw25508Labels = mixedMoment B raw25508step0 raw25508step0Labels := by
      have ha : raw25508step0 = (fun i j => raw25508 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25508step0 raw25508; decide +kernel
      have hl : raw25508step0Labels = raw25508Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25508 raw25508Labels permutation176 permutation2
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw25509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25509 raw25509Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw25509 raw25509Labels = mixedMoment B raw25509step0 raw25509step0Labels := by
      have ha : raw25509step0 = (fun i j => raw25509 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25509step0 raw25509; decide +kernel
      have hl : raw25509step0Labels = raw25509Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25509 raw25509Labels permutation178 permutation2
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw25510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25510 raw25510Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw25510 raw25510Labels = mixedMoment B raw25510step0 raw25510step0Labels := by
      have ha : raw25510step0 = (fun i j => raw25510 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25510step0 raw25510; decide +kernel
      have hl : raw25510step0Labels = raw25510Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25510 raw25510Labels permutation181 permutation2
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw25511 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]
def raw25511Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25511step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw25511step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25511step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25511step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25511 raw25511Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw25511 raw25511Labels = mixedMoment B raw25511step0 raw25511step0Labels := by
      have hz : ∀ j, raw25511 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw25511step0 = (fun i j => raw25511 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw25511step0 raw25511; decide +kernel
      have hl : raw25511step0Labels = raw25511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25511 raw25511Labels permutation590 hz
    mixedMoment B raw25511step0 raw25511step0Labels = mixedMoment B raw25511step1 raw25511step1Labels := by
      have ha : raw25511step1 = (fun i j => raw25511step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25511step1 raw25511step0; decide +kernel
      have hl : raw25511step1Labels = raw25511step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25511step0 raw25511step0Labels permutation39 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw25512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25512 raw25512Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw25512 raw25512Labels = mixedMoment B raw25512step0 raw25512step0Labels := by
      have ha : raw25512step0 = (fun i j => raw25512 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25512step0 raw25512; decide +kernel
      have hl : raw25512step0Labels = raw25512Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25512 raw25512Labels permutation195 permutation2
    _ = mixedMoment B node998 node998Labels := by rfl

def raw25513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25513 raw25513Labels = mixedMoment B node1032 node1032Labels := by
  calc
    mixedMoment B raw25513 raw25513Labels = mixedMoment B raw25513step0 raw25513step0Labels := by
      have ha : raw25513step0 = (fun i j => raw25513 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25513step0 raw25513; decide +kernel
      have hl : raw25513step0Labels = raw25513Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25513 raw25513Labels permutation157 permutation2
    _ = mixedMoment B node1032 node1032Labels := by rfl

def raw25514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25514 raw25514Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw25514 raw25514Labels = mixedMoment B raw25514step0 raw25514step0Labels := by
      have ha : raw25514step0 = (fun i j => raw25514 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25514step0 raw25514; decide +kernel
      have hl : raw25514step0Labels = raw25514Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25514 raw25514Labels permutation181 permutation2
    _ = mixedMoment B node977 node977Labels := by rfl

def raw25515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25515 raw25515Labels = mixedMoment B node978 node978Labels := by
  calc
    mixedMoment B raw25515 raw25515Labels = mixedMoment B raw25515step0 raw25515step0Labels := by
      have ha : raw25515step0 = (fun i j => raw25515 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25515step0 raw25515; decide +kernel
      have hl : raw25515step0Labels = raw25515Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25515 raw25515Labels permutation180 permutation2
    _ = mixedMoment B node978 node978Labels := by rfl

def raw25516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25516 raw25516Labels = mixedMoment B node978 node978Labels := by
  calc
    mixedMoment B raw25516 raw25516Labels = mixedMoment B raw25516step0 raw25516step0Labels := by
      have ha : raw25516step0 = (fun i j => raw25516 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25516step0 raw25516; decide +kernel
      have hl : raw25516step0Labels = raw25516Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25516 raw25516Labels permutation178 permutation2
    _ = mixedMoment B node978 node978Labels := by rfl

def raw25517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25517 raw25517Labels = mixedMoment B node2076 node2076Labels := by
  calc
    mixedMoment B raw25517 raw25517Labels = mixedMoment B raw25517step0 raw25517step0Labels := by
      have ha : raw25517step0 = (fun i j => raw25517 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25517step0 raw25517; decide +kernel
      have hl : raw25517step0Labels = raw25517Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25517 raw25517Labels permutation154 permutation2
    _ = mixedMoment B node2076 node2076Labels := by rfl

def raw25518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25518 raw25518Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw25518 raw25518Labels = mixedMoment B raw25518step0 raw25518step0Labels := by
      have ha : raw25518step0 = (fun i j => raw25518 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25518step0 raw25518; decide +kernel
      have hl : raw25518step0Labels = raw25518Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25518 raw25518Labels permutation178 permutation2
    _ = mixedMoment B node1909 node1909Labels := by rfl

def raw25519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25519 raw25519Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw25519 raw25519Labels = mixedMoment B raw25519step0 raw25519step0Labels := by
      have ha : raw25519step0 = (fun i j => raw25519 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25519step0 raw25519; decide +kernel
      have hl : raw25519step0Labels = raw25519Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25519 raw25519Labels permutation176 permutation2
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw25520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25520 raw25520Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw25520 raw25520Labels = mixedMoment B raw25520step0 raw25520step0Labels := by
      have hz : ∀ j, raw25520 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25520step0 = (fun i j => raw25520 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25520step0 raw25520; decide +kernel
      have hl : raw25520step0Labels = raw25520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25520 raw25520Labels permutation520 hz
    mixedMoment B raw25520step0 raw25520step0Labels = mixedMoment B raw25520step1 raw25520step1Labels := by
      have ha : raw25520step1 = (fun i j => raw25520step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25520step1 raw25520step0; decide +kernel
      have hl : raw25520step1Labels = raw25520step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25520step0 raw25520step0Labels permutation38 permutation2
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw25521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25521 raw25521Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw25521 raw25521Labels = mixedMoment B raw25521step0 raw25521step0Labels := by
      have ha : raw25521step0 = (fun i j => raw25521 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25521step0 raw25521; decide +kernel
      have hl : raw25521step0Labels = raw25521Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25521 raw25521Labels permutation179 permutation2
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw25522 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]
def raw25522Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25522step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw25522step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25522step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25522step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25522 raw25522Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw25522 raw25522Labels = mixedMoment B raw25522step0 raw25522step0Labels := by
      have hz : ∀ j, raw25522 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25522step0 = (fun i j => raw25522 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25522step0 raw25522; decide +kernel
      have hl : raw25522step0Labels = raw25522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25522 raw25522Labels permutation520 hz
    mixedMoment B raw25522step0 raw25522step0Labels = mixedMoment B raw25522step1 raw25522step1Labels := by
      have ha : raw25522step1 = (fun i j => raw25522step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25522step1 raw25522step0; decide +kernel
      have hl : raw25522step1Labels = raw25522step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25522step0 raw25522step0Labels permutation39 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw25523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25523 raw25523Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw25523 raw25523Labels = mixedMoment B raw25523step0 raw25523step0Labels := by
      have ha : raw25523step0 = (fun i j => raw25523 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25523step0 raw25523; decide +kernel
      have hl : raw25523step0Labels = raw25523Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25523 raw25523Labels permutation176 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

def raw25524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25524 raw25524Labels = mixedMoment B node2077 node2077Labels := by
  calc
    _ = mixedMoment B node2077 node2077Labels := by rfl

def raw25525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25525 raw25525Labels = mixedMoment B node1912 node1912Labels := by
  calc
    mixedMoment B raw25525 raw25525Labels = mixedMoment B raw25525step0 raw25525step0Labels := by
      have ha : raw25525step0 = (fun i j => raw25525 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25525step0 raw25525; decide +kernel
      have hl : raw25525step0Labels = raw25525Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25525 raw25525Labels permutation176 permutation2
    _ = mixedMoment B node1912 node1912Labels := by rfl

def raw25526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25526 raw25526Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw25526 raw25526Labels = mixedMoment B raw25526step0 raw25526step0Labels := by
      have ha : raw25526step0 = (fun i j => raw25526 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25526step0 raw25526; decide +kernel
      have hl : raw25526step0Labels = raw25526Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25526 raw25526Labels permutation176 permutation2
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw25527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25527 raw25527Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw25527 raw25527Labels = mixedMoment B raw25527step0 raw25527step0Labels := by
      have ha : raw25527step0 = (fun i j => raw25527 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25527step0 raw25527; decide +kernel
      have hl : raw25527step0Labels = raw25527Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25527 raw25527Labels permutation178 permutation2
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw25528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25528 raw25528Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw25528 raw25528Labels = mixedMoment B raw25528step0 raw25528step0Labels := by
      have ha : raw25528step0 = (fun i j => raw25528 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25528step0 raw25528; decide +kernel
      have hl : raw25528step0Labels = raw25528Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25528 raw25528Labels permutation176 permutation2
    _ = mixedMoment B node2204 node2204Labels := by rfl

def raw25529 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw25529Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25529step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw25529step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25529 raw25529Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw25529 raw25529Labels = mixedMoment B raw25529step0 raw25529step0Labels := by
      have ha : raw25529step0 = (fun i j => raw25529 (permutation176 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25529step0 raw25529; decide +kernel
      have hl : raw25529step0Labels = raw25529Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25529 raw25529Labels permutation176 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw25530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25530 raw25530Labels = mixedMoment B node571 node571Labels := by
  calc
    mixedMoment B raw25530 raw25530Labels = mixedMoment B raw25530step0 raw25530step0Labels := by
      have ha : raw25530step0 = (fun i j => raw25530 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25530step0 raw25530; decide +kernel
      have hl : raw25530step0Labels = raw25530Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25530 raw25530Labels permutation176 permutation2
    _ = mixedMoment B node571 node571Labels := by rfl

def raw25531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25531 raw25531Labels = mixedMoment B node884 node884Labels := by
  calc
    mixedMoment B raw25531 raw25531Labels = mixedMoment B raw25531step0 raw25531step0Labels := by
      have ha : raw25531step0 = (fun i j => raw25531 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25531step0 raw25531; decide +kernel
      have hl : raw25531step0Labels = raw25531Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25531 raw25531Labels permutation176 permutation2
    _ = mixedMoment B node884 node884Labels := by rfl

def raw25532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25532 raw25532Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw25532 raw25532Labels = mixedMoment B raw25532step0 raw25532step0Labels := by
      have ha : raw25532step0 = (fun i j => raw25532 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25532step0 raw25532; decide +kernel
      have hl : raw25532step0Labels = raw25532Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25532 raw25532Labels permutation182 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

def raw25533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25533 raw25533Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw25533 raw25533Labels = mixedMoment B raw25533step0 raw25533step0Labels := by
      have ha : raw25533step0 = (fun i j => raw25533 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25533step0 raw25533; decide +kernel
      have hl : raw25533step0Labels = raw25533Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25533 raw25533Labels permutation188 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

def raw25534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25534 raw25534Labels = mixedMoment B node1003 node1003Labels := by
  calc
    mixedMoment B raw25534 raw25534Labels = mixedMoment B raw25534step0 raw25534step0Labels := by
      have ha : raw25534step0 = (fun i j => raw25534 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25534step0 raw25534; decide +kernel
      have hl : raw25534step0Labels = raw25534Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25534 raw25534Labels permutation176 permutation2
    _ = mixedMoment B node1003 node1003Labels := by rfl

def raw25535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25535 raw25535Labels = mixedMoment B node870 node870Labels := by
  calc
    mixedMoment B raw25535 raw25535Labels = mixedMoment B raw25535step0 raw25535step0Labels := by
      have ha : raw25535step0 = (fun i j => raw25535 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25535step0 raw25535; decide +kernel
      have hl : raw25535step0Labels = raw25535Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25535 raw25535Labels permutation178 permutation2
    _ = mixedMoment B node870 node870Labels := by rfl

def raw25536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25536 raw25536Labels = mixedMoment B node870 node870Labels := by
  calc
    mixedMoment B raw25536 raw25536Labels = mixedMoment B raw25536step0 raw25536step0Labels := by
      have ha : raw25536step0 = (fun i j => raw25536 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25536step0 raw25536; decide +kernel
      have hl : raw25536step0Labels = raw25536Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25536 raw25536Labels permutation176 permutation2
    _ = mixedMoment B node870 node870Labels := by rfl

def raw25537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25537 raw25537Labels = mixedMoment B node868 node868Labels := by
  calc
    mixedMoment B raw25537 raw25537Labels = mixedMoment B raw25537step0 raw25537step0Labels := by
      have ha : raw25537step0 = (fun i j => raw25537 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25537step0 raw25537; decide +kernel
      have hl : raw25537step0Labels = raw25537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25537 raw25537Labels permutation176 permutation2
    _ = mixedMoment B node868 node868Labels := by rfl

def raw25538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25538 raw25538Labels = mixedMoment B node1034 node1034Labels := by
  calc
    _ = mixedMoment B node1034 node1034Labels := by rfl

def raw25539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25539 raw25539Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw25539 raw25539Labels = mixedMoment B raw25539step0 raw25539step0Labels := by
      have ha : raw25539step0 = (fun i j => raw25539 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25539step0 raw25539; decide +kernel
      have hl : raw25539step0Labels = raw25539Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25539 raw25539Labels permutation179 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

def raw25540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25540 raw25540Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw25540 raw25540Labels = mixedMoment B raw25540step0 raw25540step0Labels := by
      have ha : raw25540step0 = (fun i j => raw25540 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25540step0 raw25540; decide +kernel
      have hl : raw25540step0Labels = raw25540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25540 raw25540Labels permutation177 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

def raw25541 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25541 raw25541Labels = mixedMoment B node1616 node1616Labels := by
  calc
    mixedMoment B raw25541 raw25541Labels = mixedMoment B raw25541step0 raw25541step0Labels := by
      have ha : raw25541step0 = (fun i j => raw25541 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25541step0 raw25541; decide +kernel
      have hl : raw25541step0Labels = raw25541Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25541 raw25541Labels permutation176 permutation4
    mixedMoment B raw25541step0 raw25541step0Labels = mixedMoment B raw25541step1 raw25541step1Labels := by
      have ha : raw25541step1 = -raw25541step0 := by apply Matrix.ext; change ∀ i j, raw25541step1 i j = -(raw25541step0 i j); unfold raw25541step1 raw25541step0; decide +kernel
      have hl : raw25541step1Labels = raw25541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1616 node1616Labels := by rfl

def raw25542 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25542 raw25542Labels = mixedMoment B node719 node719Labels := by
  calc
    mixedMoment B raw25542 raw25542Labels = mixedMoment B raw25542step0 raw25542step0Labels := by
      have ha : raw25542step0 = (fun i j => raw25542 (permutation185 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25542step0 raw25542; decide +kernel
      have hl : raw25542step0Labels = raw25542Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25542 raw25542Labels permutation185 permutation4
    mixedMoment B raw25542step0 raw25542step0Labels = mixedMoment B raw25542step1 raw25542step1Labels := by
      have ha : raw25542step1 = -raw25542step0 := by apply Matrix.ext; change ∀ i j, raw25542step1 i j = -(raw25542step0 i j); unfold raw25542step1 raw25542step0; decide +kernel
      have hl : raw25542step1Labels = raw25542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node719 node719Labels := by rfl

def raw25543 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25543 raw25543Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw25543 raw25543Labels = mixedMoment B raw25543step0 raw25543step0Labels := by
      have hz : ∀ j, raw25543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25543step0 = (fun i j => raw25543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25543step0 raw25543; decide +kernel
      have hl : raw25543step0Labels = raw25543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25543 raw25543Labels permutation346 hz
    mixedMoment B raw25543step0 raw25543step0Labels = mixedMoment B raw25543step1 raw25543step1Labels := by
      have ha : raw25543step1 = (fun i j => raw25543step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25543step1 raw25543step0; decide +kernel
      have hl : raw25543step1Labels = raw25543step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25543step0 raw25543step0Labels permutation32 permutation4
    mixedMoment B raw25543step1 raw25543step1Labels = mixedMoment B raw25543step2 raw25543step2Labels := by
      have ha : raw25543step2 = -raw25543step1 := by apply Matrix.ext; change ∀ i j, raw25543step2 i j = -(raw25543step1 i j); unfold raw25543step2 raw25543step1; decide +kernel
      have hl : raw25543step2Labels = raw25543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node850 node850Labels := by rfl

def raw25544 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25544 raw25544Labels = mixedMoment B node713 node713Labels := by
  calc
    mixedMoment B raw25544 raw25544Labels = mixedMoment B raw25544step0 raw25544step0Labels := by
      have ha : raw25544step0 = (fun i j => raw25544 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25544step0 raw25544; decide +kernel
      have hl : raw25544step0Labels = raw25544Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25544 raw25544Labels permutation179 permutation4
    mixedMoment B raw25544step0 raw25544step0Labels = mixedMoment B raw25544step1 raw25544step1Labels := by
      have ha : raw25544step1 = -raw25544step0 := by apply Matrix.ext; change ∀ i j, raw25544step1 i j = -(raw25544step0 i j); unfold raw25544step1 raw25544step0; decide +kernel
      have hl : raw25544step1Labels = raw25544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node713 node713Labels := by rfl

def raw25545 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw25545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25545 raw25545Labels = mixedMoment B node713 node713Labels := by
  calc
    mixedMoment B raw25545 raw25545Labels = mixedMoment B raw25545step0 raw25545step0Labels := by
      have ha : raw25545step0 = (fun i j => raw25545 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25545step0 raw25545; decide +kernel
      have hl : raw25545step0Labels = raw25545Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25545 raw25545Labels permutation177 permutation4
    mixedMoment B raw25545step0 raw25545step0Labels = mixedMoment B raw25545step1 raw25545step1Labels := by
      have ha : raw25545step1 = -raw25545step0 := by apply Matrix.ext; change ∀ i j, raw25545step1 i j = -(raw25545step0 i j); unfold raw25545step1 raw25545step0; decide +kernel
      have hl : raw25545step1Labels = raw25545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node713 node713Labels := by rfl

def raw25546 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25546 raw25546Labels = mixedMoment B node712 node712Labels := by
  calc
    mixedMoment B raw25546 raw25546Labels = mixedMoment B raw25546step0 raw25546step0Labels := by
      have ha : raw25546step0 = (fun i j => raw25546 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25546step0 raw25546; decide +kernel
      have hl : raw25546step0Labels = raw25546Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25546 raw25546Labels permutation176 permutation4
    mixedMoment B raw25546step0 raw25546step0Labels = mixedMoment B raw25546step1 raw25546step1Labels := by
      have ha : raw25546step1 = -raw25546step0 := by apply Matrix.ext; change ∀ i j, raw25546step1 i j = -(raw25546step0 i j); unfold raw25546step1 raw25546step0; decide +kernel
      have hl : raw25546step1Labels = raw25546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node712 node712Labels := by rfl

def raw25547 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25547 raw25547Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw25547 raw25547Labels = mixedMoment B raw25547step0 raw25547step0Labels := by
      have ha : raw25547step0 = (fun i j => raw25547 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25547step0 raw25547; decide +kernel
      have hl : raw25547step0Labels = raw25547Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25547 raw25547Labels permutation182 permutation4
    mixedMoment B raw25547step0 raw25547step0Labels = mixedMoment B raw25547step1 raw25547step1Labels := by
      have ha : raw25547step1 = -raw25547step0 := by apply Matrix.ext; change ∀ i j, raw25547step1 i j = -(raw25547step0 i j); unfold raw25547step1 raw25547step0; decide +kernel
      have hl : raw25547step1Labels = raw25547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1597 node1597Labels := by rfl

def raw25548 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25548 raw25548Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw25548 raw25548Labels = mixedMoment B raw25548step0 raw25548step0Labels := by
      have ha : raw25548step0 = (fun i j => raw25548 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25548step0 raw25548; decide +kernel
      have hl : raw25548step0Labels = raw25548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25548 raw25548Labels permutation188 permutation4
    mixedMoment B raw25548step0 raw25548step0Labels = mixedMoment B raw25548step1 raw25548step1Labels := by
      have ha : raw25548step1 = -raw25548step0 := by apply Matrix.ext; change ∀ i j, raw25548step1 i j = -(raw25548step0 i j); unfold raw25548step1 raw25548step0; decide +kernel
      have hl : raw25548step1Labels = raw25548step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1597 node1597Labels := by rfl

def raw25549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25549 raw25549Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw25549 raw25549Labels = mixedMoment B raw25549step0 raw25549step0Labels := by
      have ha : raw25549step0 = (fun i j => raw25549 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25549step0 raw25549; decide +kernel
      have hl : raw25549step0Labels = raw25549Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25549 raw25549Labels permutation178 permutation2
    _ = mixedMoment B node977 node977Labels := by rfl

def raw25550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25550 raw25550Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw25550 raw25550Labels = mixedMoment B raw25550step0 raw25550step0Labels := by
      have ha : raw25550step0 = (fun i j => raw25550 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25550step0 raw25550; decide +kernel
      have hl : raw25550step0Labels = raw25550Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25550 raw25550Labels permutation154 permutation2
    _ = mixedMoment B node2075 node2075Labels := by rfl

def raw25551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25551 raw25551Labels = mixedMoment B node1908 node1908Labels := by
  calc
    mixedMoment B raw25551 raw25551Labels = mixedMoment B raw25551step0 raw25551step0Labels := by
      have ha : raw25551step0 = (fun i j => raw25551 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25551step0 raw25551; decide +kernel
      have hl : raw25551step0Labels = raw25551Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25551 raw25551Labels permutation178 permutation2
    _ = mixedMoment B node1908 node1908Labels := by rfl

def raw25552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25552 raw25552Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw25552 raw25552Labels = mixedMoment B raw25552step0 raw25552step0Labels := by
      have ha : raw25552step0 = (fun i j => raw25552 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25552step0 raw25552; decide +kernel
      have hl : raw25552step0Labels = raw25552Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25552 raw25552Labels permutation176 permutation2
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw25553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25553 raw25553Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw25553 raw25553Labels = mixedMoment B raw25553step0 raw25553step0Labels := by
      have hz : ∀ j, raw25553 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25553step0 = (fun i j => raw25553 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25553step0 raw25553; decide +kernel
      have hl : raw25553step0Labels = raw25553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25553 raw25553Labels permutation520 hz
    mixedMoment B raw25553step0 raw25553step0Labels = mixedMoment B raw25553step1 raw25553step1Labels := by
      have ha : raw25553step1 = (fun i j => raw25553step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25553step1 raw25553step0; decide +kernel
      have hl : raw25553step1Labels = raw25553step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25553step0 raw25553step0Labels permutation38 permutation2
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw25554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25554 raw25554Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw25554 raw25554Labels = mixedMoment B raw25554step0 raw25554step0Labels := by
      have ha : raw25554step0 = (fun i j => raw25554 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25554step0 raw25554; decide +kernel
      have hl : raw25554step0Labels = raw25554Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25554 raw25554Labels permutation178 permutation2
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw25555 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw25555Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25555step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw25555step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25555step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25555step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25555 raw25555Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw25555 raw25555Labels = mixedMoment B raw25555step0 raw25555step0Labels := by
      have hz : ∀ j, raw25555 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25555step0 = (fun i j => raw25555 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25555step0 raw25555; decide +kernel
      have hl : raw25555step0Labels = raw25555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25555 raw25555Labels permutation520 hz
    mixedMoment B raw25555step0 raw25555step0Labels = mixedMoment B raw25555step1 raw25555step1Labels := by
      have ha : raw25555step1 = (fun i j => raw25555step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25555step1 raw25555step0; decide +kernel
      have hl : raw25555step1Labels = raw25555step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25555step0 raw25555step0Labels permutation38 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw25556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25556 raw25556Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw25556 raw25556Labels = mixedMoment B raw25556step0 raw25556step0Labels := by
      have ha : raw25556step0 = (fun i j => raw25556 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25556step0 raw25556; decide +kernel
      have hl : raw25556step0Labels = raw25556Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25556 raw25556Labels permutation188 permutation2
    _ = mixedMoment B node567 node567Labels := by rfl

def raw25557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25557 raw25557Labels = mixedMoment B node878 node878Labels := by
  calc
    mixedMoment B raw25557 raw25557Labels = mixedMoment B raw25557step0 raw25557step0Labels := by
      have ha : raw25557step0 = (fun i j => raw25557 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25557step0 raw25557; decide +kernel
      have hl : raw25557step0Labels = raw25557Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25557 raw25557Labels permutation188 permutation2
    _ = mixedMoment B node878 node878Labels := by rfl

def raw25558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25558 raw25558Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw25558 raw25558Labels = mixedMoment B raw25558step0 raw25558step0Labels := by
      have ha : raw25558step0 = (fun i j => raw25558 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25558step0 raw25558; decide +kernel
      have hl : raw25558step0Labels = raw25558Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25558 raw25558Labels permutation184 permutation2
    _ = mixedMoment B node977 node977Labels := by rfl

def raw25559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25559 raw25559Labels = mixedMoment B node1004 node1004Labels := by
  calc
    mixedMoment B raw25559 raw25559Labels = mixedMoment B raw25559step0 raw25559step0Labels := by
      have hz : ∀ j, raw25559 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25559step0 = (fun i j => raw25559 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25559step0 raw25559; decide +kernel
      have hl : raw25559step0Labels = raw25559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25559 raw25559Labels permutation520 hz
    mixedMoment B raw25559step0 raw25559step0Labels = mixedMoment B raw25559step1 raw25559step1Labels := by
      have ha : raw25559step1 = (fun i j => raw25559step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25559step1 raw25559step0; decide +kernel
      have hl : raw25559step1Labels = raw25559step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25559step0 raw25559step0Labels permutation38 permutation2
    _ = mixedMoment B node1004 node1004Labels := by rfl

def raw25560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25560 raw25560Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw25560 raw25560Labels = mixedMoment B raw25560step0 raw25560step0Labels := by
      have ha : raw25560step0 = (fun i j => raw25560 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25560step0 raw25560; decide +kernel
      have hl : raw25560step0Labels = raw25560Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25560 raw25560Labels permutation188 permutation2
    _ = mixedMoment B node998 node998Labels := by rfl

def raw25561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25561 raw25561Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw25561 raw25561Labels = mixedMoment B raw25561step0 raw25561step0Labels := by
      have ha : raw25561step0 = (fun i j => raw25561 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25561step0 raw25561; decide +kernel
      have hl : raw25561step0Labels = raw25561Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25561 raw25561Labels permutation178 permutation2
    _ = mixedMoment B node866 node866Labels := by rfl

def raw25562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25562 raw25562Labels = mixedMoment B node869 node869Labels := by
  calc
    mixedMoment B raw25562 raw25562Labels = mixedMoment B raw25562step0 raw25562step0Labels := by
      have ha : raw25562step0 = (fun i j => raw25562 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25562step0 raw25562; decide +kernel
      have hl : raw25562step0Labels = raw25562Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25562 raw25562Labels permutation176 permutation2
    _ = mixedMoment B node869 node869Labels := by rfl

def raw25563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25563 raw25563Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw25563 raw25563Labels = mixedMoment B raw25563step0 raw25563step0Labels := by
      have ha : raw25563step0 = (fun i j => raw25563 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25563step0 raw25563; decide +kernel
      have hl : raw25563step0Labels = raw25563Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25563 raw25563Labels permutation178 permutation2
    _ = mixedMoment B node865 node865Labels := by rfl

def raw25564 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw25564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25564 raw25564Labels = mixedMoment B node703 node703Labels := by
  calc
    mixedMoment B raw25564 raw25564Labels = mixedMoment B raw25564step0 raw25564step0Labels := by
      have ha : raw25564step0 = (fun i j => raw25564 (permutation190 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25564step0 raw25564; decide +kernel
      have hl : raw25564step0Labels = raw25564Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25564 raw25564Labels permutation190 permutation4
    mixedMoment B raw25564step0 raw25564step0Labels = mixedMoment B raw25564step1 raw25564step1Labels := by
      have ha : raw25564step1 = -raw25564step0 := by apply Matrix.ext; change ∀ i j, raw25564step1 i j = -(raw25564step0 i j); unfold raw25564step1 raw25564step0; decide +kernel
      have hl : raw25564step1Labels = raw25564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node703 node703Labels := by rfl

def raw25565 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw25565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25565 raw25565Labels = mixedMoment B node700 node700Labels := by
  calc
    mixedMoment B raw25565 raw25565Labels = mixedMoment B raw25565step0 raw25565step0Labels := by
      have ha : raw25565step0 = (fun i j => raw25565 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25565step0 raw25565; decide +kernel
      have hl : raw25565step0Labels = raw25565Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25565 raw25565Labels permutation188 permutation4
    mixedMoment B raw25565step0 raw25565step0Labels = mixedMoment B raw25565step1 raw25565step1Labels := by
      have ha : raw25565step1 = -raw25565step0 := by apply Matrix.ext; change ∀ i j, raw25565step1 i j = -(raw25565step0 i j); unfold raw25565step1 raw25565step0; decide +kernel
      have hl : raw25565step1Labels = raw25565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node700 node700Labels := by rfl

def raw25566 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw25566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25566 raw25566Labels = mixedMoment B node699 node699Labels := by
  calc
    mixedMoment B raw25566 raw25566Labels = mixedMoment B raw25566step0 raw25566step0Labels := by
      have ha : raw25566step0 = (fun i j => raw25566 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25566step0 raw25566; decide +kernel
      have hl : raw25566step0Labels = raw25566Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25566 raw25566Labels permutation188 permutation4
    mixedMoment B raw25566step0 raw25566step0Labels = mixedMoment B raw25566step1 raw25566step1Labels := by
      have ha : raw25566step1 = -raw25566step0 := by apply Matrix.ext; change ∀ i j, raw25566step1 i j = -(raw25566step0 i j); unfold raw25566step1 raw25566step0; decide +kernel
      have hl : raw25566step1Labels = raw25566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node699 node699Labels := by rfl

def raw25567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25567 raw25567Labels = mixedMoment B node976 node976Labels := by
  calc
    mixedMoment B raw25567 raw25567Labels = mixedMoment B raw25567step0 raw25567step0Labels := by
      have ha : raw25567step0 = (fun i j => raw25567 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25567step0 raw25567; decide +kernel
      have hl : raw25567step0Labels = raw25567Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25567 raw25567Labels permutation176 permutation2
    _ = mixedMoment B node976 node976Labels := by rfl

def raw25568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25568 raw25568Labels = mixedMoment B node2074 node2074Labels := by
  calc
    _ = mixedMoment B node2074 node2074Labels := by rfl

def raw25569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25569 raw25569Labels = mixedMoment B node1907 node1907Labels := by
  calc
    mixedMoment B raw25569 raw25569Labels = mixedMoment B raw25569step0 raw25569step0Labels := by
      have ha : raw25569step0 = (fun i j => raw25569 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25569step0 raw25569; decide +kernel
      have hl : raw25569step0Labels = raw25569Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25569 raw25569Labels permutation176 permutation2
    _ = mixedMoment B node1907 node1907Labels := by rfl

def raw25570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25570 raw25570Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw25570 raw25570Labels = mixedMoment B raw25570step0 raw25570step0Labels := by
      have hz : ∀ j, raw25570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw25570step0 = (fun i j => raw25570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw25570step0 raw25570; decide +kernel
      have hl : raw25570step0Labels = raw25570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25570 raw25570Labels permutation434 hz
    mixedMoment B raw25570step0 raw25570step0Labels = mixedMoment B raw25570step1 raw25570step1Labels := by
      have ha : raw25570step1 = (fun i j => raw25570step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25570step1 raw25570step0; decide +kernel
      have hl : raw25570step1Labels = raw25570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25570step0 raw25570step0Labels permutation38 permutation2
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw25571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25571 raw25571Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw25571 raw25571Labels = mixedMoment B raw25571step0 raw25571step0Labels := by
      have hz : ∀ j, raw25571 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25571step0 = (fun i j => raw25571 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25571step0 raw25571; decide +kernel
      have hl : raw25571step0Labels = raw25571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25571 raw25571Labels permutation520 hz
    mixedMoment B raw25571step0 raw25571step0Labels = mixedMoment B raw25571step1 raw25571step1Labels := by
      have ha : raw25571step1 = (fun i j => raw25571step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25571step1 raw25571step0; decide +kernel
      have hl : raw25571step1Labels = raw25571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25571step0 raw25571step0Labels permutation38 permutation2
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw25572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25572 raw25572Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw25572 raw25572Labels = mixedMoment B raw25572step0 raw25572step0Labels := by
      have ha : raw25572step0 = (fun i j => raw25572 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25572step0 raw25572; decide +kernel
      have hl : raw25572step0Labels = raw25572Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25572 raw25572Labels permutation176 permutation2
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw25573 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw25573Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25573step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![0, 0], ![3, -3]]
def raw25573step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25573step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw25573step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25573step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw25573step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25573 raw25573Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw25573 raw25573Labels = mixedMoment B raw25573step0 raw25573step0Labels := by
      have hz : ∀ j, raw25573 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25573step0 = (fun i j => raw25573 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25573step0 raw25573; decide +kernel
      have hl : raw25573step0Labels = raw25573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25573 raw25573Labels permutation520 hz
    mixedMoment B raw25573step0 raw25573step0Labels = mixedMoment B raw25573step1 raw25573step1Labels := by
      have hz : ∀ j, raw25573step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw25573step1 = (fun i j => raw25573step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw25573step1 raw25573step0; decide +kernel
      have hl : raw25573step1Labels = raw25573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25573step0 raw25573step0Labels permutation104 hz
    mixedMoment B raw25573step1 raw25573step1Labels = mixedMoment B raw25573step2 raw25573step2Labels := by
      have ha : raw25573step2 = (fun i j => raw25573step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25573step2 raw25573step1; decide +kernel
      have hl : raw25573step2Labels = raw25573step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25573step1 raw25573step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw25574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![2, -3, 1]]
def raw25574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![2, -3, 1]]
def raw25574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![1, 0, -1], ![2, -3, 1]]
def raw25574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw25574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25574 raw25574Labels = mixedMoment B node1088 node1088Labels := by
  calc
    mixedMoment B raw25574 raw25574Labels = mixedMoment B raw25574step0 raw25574step0Labels := by
      have hz : ∀ j, raw25574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25574step0 = (fun i j => raw25574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25574step0 raw25574; decide +kernel
      have hl : raw25574step0Labels = raw25574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25574 raw25574Labels permutation346 hz
    mixedMoment B raw25574step0 raw25574step0Labels = mixedMoment B raw25574step1 raw25574step1Labels := by
      have hz : ∀ j, raw25574step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25574step1 = (fun i j => raw25574step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25574step1 raw25574step0; decide +kernel
      have hl : raw25574step1Labels = raw25574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25574step0 raw25574step0Labels permutation56 hz
    mixedMoment B raw25574step1 raw25574step1Labels = mixedMoment B raw25574step2 raw25574step2Labels := by
      have ha : raw25574step2 = (fun i j => raw25574step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25574step2 raw25574step1; decide +kernel
      have hl : raw25574step2Labels = raw25574step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25574step1 raw25574step1Labels permutation10 permutation2
    _ = mixedMoment B node1088 node1088Labels := by rfl

def raw25575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![2, -3, 1]]
def raw25575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![2, -3, 1]]
def raw25575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw25575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25575 raw25575Labels = mixedMoment B node2059 node2059Labels := by
  calc
    mixedMoment B raw25575 raw25575Labels = mixedMoment B raw25575step0 raw25575step0Labels := by
      have hz : ∀ j, raw25575 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25575step0 = (fun i j => raw25575 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25575step0 raw25575; decide +kernel
      have hl : raw25575step0Labels = raw25575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25575 raw25575Labels permutation346 hz
    mixedMoment B raw25575step0 raw25575step0Labels = mixedMoment B raw25575step1 raw25575step1Labels := by
      have ha : raw25575step1 = (fun i j => raw25575step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25575step1 raw25575step0; decide +kernel
      have hl : raw25575step1Labels = raw25575step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25575step0 raw25575step0Labels permutation34 permutation2
    _ = mixedMoment B node2059 node2059Labels := by rfl

def raw25576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![2, -3, 1]]
def raw25576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![2, -3, 1]]
def raw25576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw25576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25576 raw25576Labels = mixedMoment B node2059 node2059Labels := by
  calc
    mixedMoment B raw25576 raw25576Labels = mixedMoment B raw25576step0 raw25576step0Labels := by
      have hz : ∀ j, raw25576 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25576step0 = (fun i j => raw25576 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25576step0 raw25576; decide +kernel
      have hl : raw25576step0Labels = raw25576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25576 raw25576Labels permutation265 hz
    mixedMoment B raw25576step0 raw25576step0Labels = mixedMoment B raw25576step1 raw25576step1Labels := by
      have ha : raw25576step1 = (fun i j => raw25576step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25576step1 raw25576step0; decide +kernel
      have hl : raw25576step1Labels = raw25576step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25576step0 raw25576step0Labels permutation34 permutation2
    _ = mixedMoment B node2059 node2059Labels := by rfl

def raw25577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw25577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw25577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw25577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw25577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw25577step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25577 raw25577Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw25577 raw25577Labels = mixedMoment B raw25577step0 raw25577step0Labels := by
      have hz : ∀ j, raw25577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25577step0 = (fun i j => raw25577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25577step0 raw25577; decide +kernel
      have hl : raw25577step0Labels = raw25577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25577 raw25577Labels permutation346 hz
    mixedMoment B raw25577step0 raw25577step0Labels = mixedMoment B raw25577step1 raw25577step1Labels := by
      have hz : ∀ j, raw25577step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25577step1 = (fun i j => raw25577step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25577step1 raw25577step0; decide +kernel
      have hl : raw25577step1Labels = raw25577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25577step0 raw25577step0Labels permutation56 hz
    mixedMoment B raw25577step1 raw25577step1Labels = mixedMoment B raw25577step2 raw25577step2Labels := by
      have ha : raw25577step2 = (fun i j => raw25577step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25577step2 raw25577step1; decide +kernel
      have hl : raw25577step2Labels = raw25577step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25577step1 raw25577step1Labels permutation16 permutation4
    mixedMoment B raw25577step2 raw25577step2Labels = mixedMoment B raw25577step3 raw25577step3Labels := by
      have ha : raw25577step3 = -raw25577step2 := by apply Matrix.ext; change ∀ i j, raw25577step3 i j = -(raw25577step2 i j); unfold raw25577step3 raw25577step2; decide +kernel
      have hl : raw25577step3Labels = raw25577step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw25578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![0, 1, -1], ![2, -3, 1]]
def raw25578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![0, 1, -1], ![2, -3, 1]]
def raw25578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![0, 1, -1], ![2, -3, 1]]
def raw25578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw25578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25578 raw25578Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw25578 raw25578Labels = mixedMoment B raw25578step0 raw25578step0Labels := by
      have hz : ∀ j, raw25578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25578step0 = (fun i j => raw25578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25578step0 raw25578; decide +kernel
      have hl : raw25578step0Labels = raw25578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25578 raw25578Labels permutation346 hz
    mixedMoment B raw25578step0 raw25578step0Labels = mixedMoment B raw25578step1 raw25578step1Labels := by
      have hz : ∀ j, raw25578step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25578step1 = (fun i j => raw25578step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25578step1 raw25578step0; decide +kernel
      have hl : raw25578step1Labels = raw25578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25578step0 raw25578step0Labels permutation56 hz
    mixedMoment B raw25578step1 raw25578step1Labels = mixedMoment B raw25578step2 raw25578step2Labels := by
      have ha : raw25578step2 = (fun i j => raw25578step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25578step2 raw25578step1; decide +kernel
      have hl : raw25578step2Labels = raw25578step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25578step1 raw25578step1Labels permutation10 permutation2
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw25579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw25579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw25579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw25579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25579 raw25579Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw25579 raw25579Labels = mixedMoment B raw25579step0 raw25579step0Labels := by
      have hz : ∀ j, raw25579 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25579step0 = (fun i j => raw25579 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25579step0 raw25579; decide +kernel
      have hl : raw25579step0Labels = raw25579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25579 raw25579Labels permutation346 hz
    mixedMoment B raw25579step0 raw25579step0Labels = mixedMoment B raw25579step1 raw25579step1Labels := by
      have hz : ∀ j, raw25579step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25579step1 = (fun i j => raw25579step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25579step1 raw25579step0; decide +kernel
      have hl : raw25579step1Labels = raw25579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25579step0 raw25579step0Labels permutation56 hz
    mixedMoment B raw25579step1 raw25579step1Labels = mixedMoment B raw25579step2 raw25579step2Labels := by
      have ha : raw25579step2 = (fun i j => raw25579step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25579step2 raw25579step1; decide +kernel
      have hl : raw25579step2Labels = raw25579step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25579step1 raw25579step1Labels permutation13 permutation2
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw25580 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3], ![1, -1], ![-1, 1]]
def raw25580Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25580step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3], ![1, -1], ![-1, 1]]
def raw25580step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25580step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![3, -3], ![1, -1], ![-1, 1]]
def raw25580step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25580step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw25580step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25580 raw25580Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw25580 raw25580Labels = mixedMoment B raw25580step0 raw25580step0Labels := by
      have hz : ∀ j, raw25580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25580step0 = (fun i j => raw25580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25580step0 raw25580; decide +kernel
      have hl : raw25580step0Labels = raw25580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25580 raw25580Labels permutation346 hz
    mixedMoment B raw25580step0 raw25580step0Labels = mixedMoment B raw25580step1 raw25580step1Labels := by
      have hz : ∀ j, raw25580step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25580step1 = (fun i j => raw25580step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25580step1 raw25580step0; decide +kernel
      have hl : raw25580step1Labels = raw25580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25580step0 raw25580step0Labels permutation56 hz
    mixedMoment B raw25580step1 raw25580step1Labels = mixedMoment B raw25580step2 raw25580step2Labels := by
      have ha : raw25580step2 = (fun i j => raw25580step1 (permutation13 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25580step2 raw25580step1; decide +kernel
      have hl : raw25580step2Labels = raw25580step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25580step1 raw25580step1Labels permutation13 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw25581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw25581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw25581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25581 raw25581Labels = mixedMoment B node1070 node1070Labels := by
  calc
    mixedMoment B raw25581 raw25581Labels = mixedMoment B raw25581step0 raw25581step0Labels := by
      have hz : ∀ j, raw25581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25581step0 = (fun i j => raw25581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25581step0 raw25581; decide +kernel
      have hl : raw25581step0Labels = raw25581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25581 raw25581Labels permutation346 hz
    mixedMoment B raw25581step0 raw25581step0Labels = mixedMoment B raw25581step1 raw25581step1Labels := by
      have ha : raw25581step1 = (fun i j => raw25581step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25581step1 raw25581step0; decide +kernel
      have hl : raw25581step1Labels = raw25581step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25581step0 raw25581step0Labels permutation51 permutation2
    _ = mixedMoment B node1070 node1070Labels := by rfl

def raw25582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw25582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw25582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25582 raw25582Labels = mixedMoment B node1070 node1070Labels := by
  calc
    mixedMoment B raw25582 raw25582Labels = mixedMoment B raw25582step0 raw25582step0Labels := by
      have hz : ∀ j, raw25582 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25582step0 = (fun i j => raw25582 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25582step0 raw25582; decide +kernel
      have hl : raw25582step0Labels = raw25582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25582 raw25582Labels permutation265 hz
    mixedMoment B raw25582step0 raw25582step0Labels = mixedMoment B raw25582step1 raw25582step1Labels := by
      have ha : raw25582step1 = (fun i j => raw25582step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25582step1 raw25582step0; decide +kernel
      have hl : raw25582step1Labels = raw25582step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25582step0 raw25582step0Labels permutation51 permutation2
    _ = mixedMoment B node1070 node1070Labels := by rfl

def raw25583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, 0, -1], ![1, -2, 1]]
def raw25583Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 1, -3], ![1, 0, -1], ![1, -2, 1]]
def raw25583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 1, -3], ![1, 0, -1], ![1, -2, 1]]
def raw25583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25583step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25583 raw25583Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw25583 raw25583Labels = mixedMoment B raw25583step0 raw25583step0Labels := by
      have hz : ∀ j, raw25583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25583step0 = (fun i j => raw25583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25583step0 raw25583; decide +kernel
      have hl : raw25583step0Labels = raw25583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25583 raw25583Labels permutation346 hz
    mixedMoment B raw25583step0 raw25583step0Labels = mixedMoment B raw25583step1 raw25583step1Labels := by
      have hz : ∀ j, raw25583step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25583step1 = (fun i j => raw25583step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25583step1 raw25583step0; decide +kernel
      have hl : raw25583step1Labels = raw25583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25583step0 raw25583step0Labels permutation56 hz
    mixedMoment B raw25583step1 raw25583step1Labels = mixedMoment B raw25583step2 raw25583step2Labels := by
      have ha : raw25583step2 = (fun i j => raw25583step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25583step2 raw25583step1; decide +kernel
      have hl : raw25583step2Labels = raw25583step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25583step1 raw25583step1Labels permutation13 permutation2
    _ = mixedMoment B node1074 node1074Labels := by rfl

def raw25584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1], ![1, -2, 1]]
def raw25584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1], ![1, -2, 1]]
def raw25584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![2, -1, -1], ![1, -2, 1]]
def raw25584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25584 raw25584Labels = mixedMoment B node1076 node1076Labels := by
  calc
    mixedMoment B raw25584 raw25584Labels = mixedMoment B raw25584step0 raw25584step0Labels := by
      have hz : ∀ j, raw25584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25584step0 = (fun i j => raw25584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25584step0 raw25584; decide +kernel
      have hl : raw25584step0Labels = raw25584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25584 raw25584Labels permutation346 hz
    mixedMoment B raw25584step0 raw25584step0Labels = mixedMoment B raw25584step1 raw25584step1Labels := by
      have hz : ∀ j, raw25584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25584step1 = (fun i j => raw25584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25584step1 raw25584step0; decide +kernel
      have hl : raw25584step1Labels = raw25584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25584step0 raw25584step0Labels permutation56 hz
    mixedMoment B raw25584step1 raw25584step1Labels = mixedMoment B raw25584step2 raw25584step2Labels := by
      have ha : raw25584step2 = (fun i j => raw25584step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25584step2 raw25584step1; decide +kernel
      have hl : raw25584step2Labels = raw25584step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25584step1 raw25584step1Labels permutation12 permutation2
    _ = mixedMoment B node1076 node1076Labels := by rfl

def raw25585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25585 raw25585Labels = mixedMoment B node1076 node1076Labels := by
  calc
    mixedMoment B raw25585 raw25585Labels = mixedMoment B raw25585step0 raw25585step0Labels := by
      have hz : ∀ j, raw25585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25585step0 = (fun i j => raw25585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25585step0 raw25585; decide +kernel
      have hl : raw25585step0Labels = raw25585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25585 raw25585Labels permutation346 hz
    mixedMoment B raw25585step0 raw25585step0Labels = mixedMoment B raw25585step1 raw25585step1Labels := by
      have hz : ∀ j, raw25585step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25585step1 = (fun i j => raw25585step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25585step1 raw25585step0; decide +kernel
      have hl : raw25585step1Labels = raw25585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25585step0 raw25585step0Labels permutation56 hz
    mixedMoment B raw25585step1 raw25585step1Labels = mixedMoment B raw25585step2 raw25585step2Labels := by
      have ha : raw25585step2 = (fun i j => raw25585step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25585step2 raw25585step1; decide +kernel
      have hl : raw25585step2Labels = raw25585step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25585step1 raw25585step1Labels permutation10 permutation2
    _ = mixedMoment B node1076 node1076Labels := by rfl

def raw25586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25586 raw25586Labels = mixedMoment B node2049 node2049Labels := by
  calc
    mixedMoment B raw25586 raw25586Labels = mixedMoment B raw25586step0 raw25586step0Labels := by
      have hz : ∀ j, raw25586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25586step0 = (fun i j => raw25586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25586step0 raw25586; decide +kernel
      have hl : raw25586step0Labels = raw25586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25586 raw25586Labels permutation346 hz
    mixedMoment B raw25586step0 raw25586step0Labels = mixedMoment B raw25586step1 raw25586step1Labels := by
      have ha : raw25586step1 = (fun i j => raw25586step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25586step1 raw25586step0; decide +kernel
      have hl : raw25586step1Labels = raw25586step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25586step0 raw25586step0Labels permutation34 permutation2
    _ = mixedMoment B node2049 node2049Labels := by rfl

def raw25587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25587 raw25587Labels = mixedMoment B node2049 node2049Labels := by
  calc
    mixedMoment B raw25587 raw25587Labels = mixedMoment B raw25587step0 raw25587step0Labels := by
      have hz : ∀ j, raw25587 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25587step0 = (fun i j => raw25587 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25587step0 raw25587; decide +kernel
      have hl : raw25587step0Labels = raw25587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25587 raw25587Labels permutation265 hz
    mixedMoment B raw25587step0 raw25587step0Labels = mixedMoment B raw25587step1 raw25587step1Labels := by
      have ha : raw25587step1 = (fun i j => raw25587step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25587step1 raw25587step0; decide +kernel
      have hl : raw25587step1Labels = raw25587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25587step0 raw25587step0Labels permutation34 permutation2
    _ = mixedMoment B node2049 node2049Labels := by rfl

def raw25588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25588 raw25588Labels = mixedMoment B node2282 node2282Labels := by
  calc
    mixedMoment B raw25588 raw25588Labels = mixedMoment B raw25588step0 raw25588step0Labels := by
      have hz : ∀ j, raw25588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25588step0 = (fun i j => raw25588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25588step0 raw25588; decide +kernel
      have hl : raw25588step0Labels = raw25588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25588 raw25588Labels permutation346 hz
    mixedMoment B raw25588step0 raw25588step0Labels = mixedMoment B raw25588step1 raw25588step1Labels := by
      have hz : ∀ j, raw25588step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25588step1 = (fun i j => raw25588step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25588step1 raw25588step0; decide +kernel
      have hl : raw25588step1Labels = raw25588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25588step0 raw25588step0Labels permutation56 hz
    _ = mixedMoment B node2282 node2282Labels := by rfl

def raw25589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![0, -1, 1], ![2, -1, -1]]
def raw25589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![0, -1, 1], ![2, -1, -1]]
def raw25589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![0, -1, 1], ![2, -1, -1]]
def raw25589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25589 raw25589Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw25589 raw25589Labels = mixedMoment B raw25589step0 raw25589step0Labels := by
      have hz : ∀ j, raw25589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25589step0 = (fun i j => raw25589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25589step0 raw25589; decide +kernel
      have hl : raw25589step0Labels = raw25589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25589 raw25589Labels permutation346 hz
    mixedMoment B raw25589step0 raw25589step0Labels = mixedMoment B raw25589step1 raw25589step1Labels := by
      have hz : ∀ j, raw25589step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25589step1 = (fun i j => raw25589step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25589step1 raw25589step0; decide +kernel
      have hl : raw25589step1Labels = raw25589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25589step0 raw25589step0Labels permutation56 hz
    mixedMoment B raw25589step1 raw25589step1Labels = mixedMoment B raw25589step2 raw25589step2Labels := by
      have ha : raw25589step2 = (fun i j => raw25589step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25589step2 raw25589step1; decide +kernel
      have hl : raw25589step2Labels = raw25589step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25589step1 raw25589step1Labels permutation10 permutation2
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw25590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![1, 0, -1]]
def raw25590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![1, 0, -1]]
def raw25590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, -2, 1], ![1, 0, -1]]
def raw25590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25590 raw25590Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw25590 raw25590Labels = mixedMoment B raw25590step0 raw25590step0Labels := by
      have hz : ∀ j, raw25590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25590step0 = (fun i j => raw25590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25590step0 raw25590; decide +kernel
      have hl : raw25590step0Labels = raw25590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25590 raw25590Labels permutation346 hz
    mixedMoment B raw25590step0 raw25590step0Labels = mixedMoment B raw25590step1 raw25590step1Labels := by
      have hz : ∀ j, raw25590step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25590step1 = (fun i j => raw25590step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25590step1 raw25590step0; decide +kernel
      have hl : raw25590step1Labels = raw25590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25590step0 raw25590step0Labels permutation56 hz
    mixedMoment B raw25590step1 raw25590step1Labels = mixedMoment B raw25590step2 raw25590step2Labels := by
      have ha : raw25590step2 = (fun i j => raw25590step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25590step2 raw25590step1; decide +kernel
      have hl : raw25590step2Labels = raw25590step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25590step1 raw25590step1Labels permutation11 permutation2
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw25591 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3], ![-1, 1], ![1, -1]]
def raw25591Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25591step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3], ![-1, 1], ![1, -1]]
def raw25591step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25591step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![3, -3], ![-1, 1], ![1, -1]]
def raw25591step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25591step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw25591step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25591 raw25591Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw25591 raw25591Labels = mixedMoment B raw25591step0 raw25591step0Labels := by
      have hz : ∀ j, raw25591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25591step0 = (fun i j => raw25591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25591step0 raw25591; decide +kernel
      have hl : raw25591step0Labels = raw25591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25591 raw25591Labels permutation346 hz
    mixedMoment B raw25591step0 raw25591step0Labels = mixedMoment B raw25591step1 raw25591step1Labels := by
      have hz : ∀ j, raw25591step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25591step1 = (fun i j => raw25591step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25591step1 raw25591step0; decide +kernel
      have hl : raw25591step1Labels = raw25591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25591step0 raw25591step0Labels permutation56 hz
    mixedMoment B raw25591step1 raw25591step1Labels = mixedMoment B raw25591step2 raw25591step2Labels := by
      have ha : raw25591step2 = (fun i j => raw25591step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25591step2 raw25591step1; decide +kernel
      have hl : raw25591step2Labels = raw25591step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25591step1 raw25591step1Labels permutation11 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw25592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25592Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25592 raw25592Labels = mixedMoment B node1090 node1090Labels := by
  calc
    mixedMoment B raw25592 raw25592Labels = mixedMoment B raw25592step0 raw25592step0Labels := by
      have hz : ∀ j, raw25592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25592step0 = (fun i j => raw25592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25592step0 raw25592; decide +kernel
      have hl : raw25592step0Labels = raw25592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25592 raw25592Labels permutation346 hz
    mixedMoment B raw25592step0 raw25592step0Labels = mixedMoment B raw25592step1 raw25592step1Labels := by
      have hz : ∀ j, raw25592step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25592step1 = (fun i j => raw25592step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25592step1 raw25592step0; decide +kernel
      have hl : raw25592step1Labels = raw25592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25592step0 raw25592step0Labels permutation56 hz
    _ = mixedMoment B node1090 node1090Labels := by rfl

def raw25593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25593 raw25593Labels = mixedMoment B node2061 node2061Labels := by
  calc
    mixedMoment B raw25593 raw25593Labels = mixedMoment B raw25593step0 raw25593step0Labels := by
      have hz : ∀ j, raw25593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25593step0 = (fun i j => raw25593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25593step0 raw25593; decide +kernel
      have hl : raw25593step0Labels = raw25593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25593 raw25593Labels permutation346 hz
    _ = mixedMoment B node2061 node2061Labels := by rfl

def raw25594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25594 raw25594Labels = mixedMoment B node2061 node2061Labels := by
  calc
    mixedMoment B raw25594 raw25594Labels = mixedMoment B raw25594step0 raw25594step0Labels := by
      have hz : ∀ j, raw25594 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25594step0 = (fun i j => raw25594 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25594step0 raw25594; decide +kernel
      have hl : raw25594step0Labels = raw25594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25594 raw25594Labels permutation265 hz
    _ = mixedMoment B node2061 node2061Labels := by rfl

def raw25595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25595Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25595 raw25595Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw25595 raw25595Labels = mixedMoment B raw25595step0 raw25595step0Labels := by
      have hz : ∀ j, raw25595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25595step0 = (fun i j => raw25595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25595step0 raw25595; decide +kernel
      have hl : raw25595step0Labels = raw25595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25595 raw25595Labels permutation346 hz
    mixedMoment B raw25595step0 raw25595step0Labels = mixedMoment B raw25595step1 raw25595step1Labels := by
      have hz : ∀ j, raw25595step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25595step1 = (fun i j => raw25595step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25595step1 raw25595step0; decide +kernel
      have hl : raw25595step1Labels = raw25595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25595step0 raw25595step0Labels permutation56 hz
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw25596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 2, -2], ![2, -3, 1]]
def raw25596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 2, -2], ![2, -3, 1]]
def raw25596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 2, -2], ![2, -3, 1]]
def raw25596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25596 raw25596Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw25596 raw25596Labels = mixedMoment B raw25596step0 raw25596step0Labels := by
      have hz : ∀ j, raw25596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25596step0 = (fun i j => raw25596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25596step0 raw25596; decide +kernel
      have hl : raw25596step0Labels = raw25596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25596 raw25596Labels permutation346 hz
    mixedMoment B raw25596step0 raw25596step0Labels = mixedMoment B raw25596step1 raw25596step1Labels := by
      have hz : ∀ j, raw25596step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25596step1 = (fun i j => raw25596step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25596step1 raw25596step0; decide +kernel
      have hl : raw25596step1Labels = raw25596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25596step0 raw25596step0Labels permutation56 hz
    mixedMoment B raw25596step1 raw25596step1Labels = mixedMoment B raw25596step2 raw25596step2Labels := by
      have ha : raw25596step2 = (fun i j => raw25596step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25596step2 raw25596step1; decide +kernel
      have hl : raw25596step2Labels = raw25596step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25596step1 raw25596step1Labels permutation10 permutation2
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw25597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw25597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw25597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw25597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw25597step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25597 raw25597Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw25597 raw25597Labels = mixedMoment B raw25597step0 raw25597step0Labels := by
      have hz : ∀ j, raw25597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25597step0 = (fun i j => raw25597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25597step0 raw25597; decide +kernel
      have hl : raw25597step0Labels = raw25597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25597 raw25597Labels permutation346 hz
    mixedMoment B raw25597step0 raw25597step0Labels = mixedMoment B raw25597step1 raw25597step1Labels := by
      have hz : ∀ j, raw25597step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25597step1 = (fun i j => raw25597step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25597step1 raw25597step0; decide +kernel
      have hl : raw25597step1Labels = raw25597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25597step0 raw25597step0Labels permutation56 hz
    mixedMoment B raw25597step1 raw25597step1Labels = mixedMoment B raw25597step2 raw25597step2Labels := by
      have ha : raw25597step2 = (fun i j => raw25597step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25597step2 raw25597step1; decide +kernel
      have hl : raw25597step2Labels = raw25597step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25597step1 raw25597step1Labels permutation12 permutation2
    _ = mixedMoment B node2288 node2288Labels := by rfl

def raw25598 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![2, -2], ![-1, 1]]
def raw25598Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25598step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![2, -2], ![-1, 1]]
def raw25598step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25598step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![2, -2], ![-1, 1]]
def raw25598step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25598step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw25598step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25598 raw25598Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw25598 raw25598Labels = mixedMoment B raw25598step0 raw25598step0Labels := by
      have hz : ∀ j, raw25598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25598step0 = (fun i j => raw25598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25598step0 raw25598; decide +kernel
      have hl : raw25598step0Labels = raw25598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25598 raw25598Labels permutation346 hz
    mixedMoment B raw25598step0 raw25598step0Labels = mixedMoment B raw25598step1 raw25598step1Labels := by
      have hz : ∀ j, raw25598step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25598step1 = (fun i j => raw25598step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25598step1 raw25598step0; decide +kernel
      have hl : raw25598step1Labels = raw25598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25598step0 raw25598step0Labels permutation56 hz
    mixedMoment B raw25598step1 raw25598step1Labels = mixedMoment B raw25598step2 raw25598step2Labels := by
      have ha : raw25598step2 = (fun i j => raw25598step1 (permutation12 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25598step2 raw25598step1; decide +kernel
      have hl : raw25598step2Labels = raw25598step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25598step1 raw25598step1Labels permutation12 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw25599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw25599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw25599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25599 raw25599Labels = mixedMoment B node1071 node1071Labels := by
  calc
    mixedMoment B raw25599 raw25599Labels = mixedMoment B raw25599step0 raw25599step0Labels := by
      have hz : ∀ j, raw25599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25599step0 = (fun i j => raw25599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25599step0 raw25599; decide +kernel
      have hl : raw25599step0Labels = raw25599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25599 raw25599Labels permutation346 hz
    mixedMoment B raw25599step0 raw25599step0Labels = mixedMoment B raw25599step1 raw25599step1Labels := by
      have ha : raw25599step1 = (fun i j => raw25599step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25599step1 raw25599step0; decide +kernel
      have hl : raw25599step1Labels = raw25599step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25599step0 raw25599step0Labels permutation50 permutation2
    _ = mixedMoment B node1071 node1071Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
