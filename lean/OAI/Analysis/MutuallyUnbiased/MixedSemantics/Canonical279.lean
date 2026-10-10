import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35712step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35712step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35712 raw35712Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw35712 raw35712Labels = mixedMoment B raw35712step0 raw35712step0Labels := by
      have ha : raw35712step0 = (fun i j => raw35712 (permutation322 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35712step0 raw35712; decide +kernel
      have hl : raw35712step0Labels = raw35712Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35712 raw35712Labels permutation322 permutation7
    mixedMoment B raw35712step0 raw35712step0Labels = mixedMoment B raw35712step1 raw35712step1Labels := by
      have ha : raw35712step1 = -raw35712step0 := by apply Matrix.ext; change ∀ i j, raw35712step1 i j = -(raw35712step0 i j); unfold raw35712step1 raw35712step0; decide +kernel
      have hl : raw35712step1Labels = raw35712step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35712step1 raw35712step1Labels = mixedMoment B raw35712step2 raw35712step2Labels := by
      have ha : raw35712step2 = raw35712step1 := by apply Matrix.ext; unfold raw35712step2 raw35712step1; decide +kernel
      have hl : raw35712step1Labels = labelEmbedding1 ∘ raw35712step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35712step1 raw35712step1Labels raw35712step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

def raw35713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35713 raw35713Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw35713 raw35713Labels = mixedMoment B raw35713step0 raw35713step0Labels := by
      have ha : raw35713step0 = (fun i j => raw35713 (permutation204 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35713step0 raw35713; decide +kernel
      have hl : raw35713step0Labels = raw35713Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35713 raw35713Labels permutation204 permutation5
    mixedMoment B raw35713step0 raw35713step0Labels = mixedMoment B raw35713step1 raw35713step1Labels := by
      have ha : raw35713step1 = -raw35713step0 := by apply Matrix.ext; change ∀ i j, raw35713step1 i j = -(raw35713step0 i j); unfold raw35713step1 raw35713step0; decide +kernel
      have hl : raw35713step1Labels = raw35713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35713step1 raw35713step1Labels = mixedMoment B raw35713step2 raw35713step2Labels := by
      have ha : raw35713step2 = raw35713step1 := by apply Matrix.ext; unfold raw35713step2 raw35713step1; decide +kernel
      have hl : raw35713step1Labels = labelEmbedding1 ∘ raw35713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35713step1 raw35713step1Labels raw35713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw35714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35714 raw35714Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw35714 raw35714Labels = mixedMoment B raw35714step0 raw35714step0Labels := by
      have ha : raw35714step0 = (fun i j => raw35714 (permutation655 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35714step0 raw35714; decide +kernel
      have hl : raw35714step0Labels = raw35714Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35714 raw35714Labels permutation655 permutation7
    mixedMoment B raw35714step0 raw35714step0Labels = mixedMoment B raw35714step1 raw35714step1Labels := by
      have ha : raw35714step1 = raw35714step0 := by apply Matrix.ext; unfold raw35714step1 raw35714step0; decide +kernel
      have hl : raw35714step0Labels = labelEmbedding1 ∘ raw35714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35714step0 raw35714step0Labels raw35714step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw35715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35715step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35715step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35715 raw35715Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw35715 raw35715Labels = mixedMoment B raw35715step0 raw35715step0Labels := by
      have ha : raw35715step0 = (fun i j => raw35715 (permutation248 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35715step0 raw35715; decide +kernel
      have hl : raw35715step0Labels = raw35715Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35715 raw35715Labels permutation248 permutation5
    mixedMoment B raw35715step0 raw35715step0Labels = mixedMoment B raw35715step1 raw35715step1Labels := by
      have ha : raw35715step1 = -raw35715step0 := by apply Matrix.ext; change ∀ i j, raw35715step1 i j = -(raw35715step0 i j); unfold raw35715step1 raw35715step0; decide +kernel
      have hl : raw35715step1Labels = raw35715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35715step1 raw35715step1Labels = mixedMoment B raw35715step2 raw35715step2Labels := by
      have ha : raw35715step2 = raw35715step1 := by apply Matrix.ext; unfold raw35715step2 raw35715step1; decide +kernel
      have hl : raw35715step1Labels = labelEmbedding1 ∘ raw35715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35715step1 raw35715step1Labels raw35715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3866 node3866Labels := by rfl

def raw35716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw35716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw35716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw35716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35716 raw35716Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw35716 raw35716Labels = mixedMoment B raw35716step0 raw35716step0Labels := by
      have hz : ∀ j, raw35716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35716step0 = (fun i j => raw35716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35716step0 raw35716; decide +kernel
      have hl : raw35716step0Labels = raw35716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35716 raw35716Labels permutation346 hz
    mixedMoment B raw35716step0 raw35716step0Labels = mixedMoment B raw35716step1 raw35716step1Labels := by
      have ha : raw35716step1 = (fun i j => raw35716step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35716step1 raw35716step0; decide +kernel
      have hl : raw35716step1Labels = raw35716step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35716step0 raw35716step0Labels permutation36 permutation5
    mixedMoment B raw35716step1 raw35716step1Labels = mixedMoment B raw35716step2 raw35716step2Labels := by
      have ha : raw35716step2 = -raw35716step1 := by apply Matrix.ext; change ∀ i j, raw35716step2 i j = -(raw35716step1 i j); unfold raw35716step2 raw35716step1; decide +kernel
      have hl : raw35716step2Labels = raw35716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35716step2 raw35716step2Labels = mixedMoment B raw35716step3 raw35716step3Labels := by
      have ha : raw35716step3 = raw35716step2 := by apply Matrix.ext; unfold raw35716step3 raw35716step2; decide +kernel
      have hl : raw35716step2Labels = labelEmbedding1 ∘ raw35716step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35716step2 raw35716step2Labels raw35716step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2158 node2158Labels := by rfl

def raw35717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw35717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw35717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35717step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw35717step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35717 raw35717Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw35717 raw35717Labels = mixedMoment B raw35717step0 raw35717step0Labels := by
      have hz : ∀ j, raw35717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35717step0 = (fun i j => raw35717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35717step0 raw35717; decide +kernel
      have hl : raw35717step0Labels = raw35717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35717 raw35717Labels permutation346 hz
    mixedMoment B raw35717step0 raw35717step0Labels = mixedMoment B raw35717step1 raw35717step1Labels := by
      have ha : raw35717step1 = (fun i j => raw35717step0 (permutation68 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35717step1 raw35717step0; decide +kernel
      have hl : raw35717step1Labels = raw35717step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35717step0 raw35717step0Labels permutation68 permutation7
    mixedMoment B raw35717step1 raw35717step1Labels = mixedMoment B raw35717step2 raw35717step2Labels := by
      have ha : raw35717step2 = -raw35717step1 := by apply Matrix.ext; change ∀ i j, raw35717step2 i j = -(raw35717step1 i j); unfold raw35717step2 raw35717step1; decide +kernel
      have hl : raw35717step2Labels = raw35717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35717step2 raw35717step2Labels = mixedMoment B raw35717step3 raw35717step3Labels := by
      have ha : raw35717step3 = raw35717step2 := by apply Matrix.ext; unfold raw35717step3 raw35717step2; decide +kernel
      have hl : raw35717step2Labels = labelEmbedding1 ∘ raw35717step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35717step2 raw35717step2Labels raw35717step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

def raw35718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35718 raw35718Labels = mixedMoment B node3760 node3760Labels := by
  calc
    mixedMoment B raw35718 raw35718Labels = mixedMoment B raw35718step0 raw35718step0Labels := by
      have ha : raw35718step0 = (fun i j => raw35718 (permutation655 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35718step0 raw35718; decide +kernel
      have hl : raw35718step0Labels = raw35718Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35718 raw35718Labels permutation655 permutation7
    mixedMoment B raw35718step0 raw35718step0Labels = mixedMoment B raw35718step1 raw35718step1Labels := by
      have ha : raw35718step1 = raw35718step0 := by apply Matrix.ext; unfold raw35718step1 raw35718step0; decide +kernel
      have hl : raw35718step0Labels = labelEmbedding1 ∘ raw35718step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35718step0 raw35718step0Labels raw35718step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3760 node3760Labels := by rfl

def raw35719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35719 raw35719Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw35719 raw35719Labels = mixedMoment B raw35719step0 raw35719step0Labels := by
      have hz : ∀ j, raw35719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35719step0 = (fun i j => raw35719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35719step0 raw35719; decide +kernel
      have hl : raw35719step0Labels = raw35719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35719 raw35719Labels permutation346 hz
    mixedMoment B raw35719step0 raw35719step0Labels = mixedMoment B raw35719step1 raw35719step1Labels := by
      have ha : raw35719step1 = (fun i j => raw35719step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35719step1 raw35719step0; decide +kernel
      have hl : raw35719step1Labels = raw35719step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35719step0 raw35719step0Labels permutation141 permutation7
    mixedMoment B raw35719step1 raw35719step1Labels = mixedMoment B raw35719step2 raw35719step2Labels := by
      have ha : raw35719step2 = raw35719step1 := by apply Matrix.ext; unfold raw35719step2 raw35719step1; decide +kernel
      have hl : raw35719step1Labels = labelEmbedding1 ∘ raw35719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35719step1 raw35719step1Labels raw35719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw35720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw35720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw35720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw35720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35720 raw35720Labels = mixedMoment B node3868 node3868Labels := by
  calc
    mixedMoment B raw35720 raw35720Labels = mixedMoment B raw35720step0 raw35720step0Labels := by
      have hz : ∀ j, raw35720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35720step0 = (fun i j => raw35720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35720step0 raw35720; decide +kernel
      have hl : raw35720step0Labels = raw35720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35720 raw35720Labels permutation346 hz
    mixedMoment B raw35720step0 raw35720step0Labels = mixedMoment B raw35720step1 raw35720step1Labels := by
      have ha : raw35720step1 = (fun i j => raw35720step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35720step1 raw35720step0; decide +kernel
      have hl : raw35720step1Labels = raw35720step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35720step0 raw35720step0Labels permutation50 permutation5
    mixedMoment B raw35720step1 raw35720step1Labels = mixedMoment B raw35720step2 raw35720step2Labels := by
      have ha : raw35720step2 = -raw35720step1 := by apply Matrix.ext; change ∀ i j, raw35720step2 i j = -(raw35720step1 i j); unfold raw35720step2 raw35720step1; decide +kernel
      have hl : raw35720step2Labels = raw35720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35720step2 raw35720step2Labels = mixedMoment B raw35720step3 raw35720step3Labels := by
      have ha : raw35720step3 = raw35720step2 := by apply Matrix.ext; unfold raw35720step3 raw35720step2; decide +kernel
      have hl : raw35720step2Labels = labelEmbedding1 ∘ raw35720step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35720step2 raw35720step2Labels raw35720step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3868 node3868Labels := by rfl

def raw35721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw35721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw35721step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35721step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw35721step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35721 raw35721Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw35721 raw35721Labels = mixedMoment B raw35721step0 raw35721step0Labels := by
      have hz : ∀ j, raw35721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35721step0 = (fun i j => raw35721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35721step0 raw35721; decide +kernel
      have hl : raw35721step0Labels = raw35721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35721 raw35721Labels permutation346 hz
    mixedMoment B raw35721step0 raw35721step0Labels = mixedMoment B raw35721step1 raw35721step1Labels := by
      have ha : raw35721step1 = (fun i j => raw35721step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35721step1 raw35721step0; decide +kernel
      have hl : raw35721step1Labels = raw35721step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35721step0 raw35721step0Labels permutation33 permutation5
    mixedMoment B raw35721step1 raw35721step1Labels = mixedMoment B raw35721step2 raw35721step2Labels := by
      have ha : raw35721step2 = -raw35721step1 := by apply Matrix.ext; change ∀ i j, raw35721step2 i j = -(raw35721step1 i j); unfold raw35721step2 raw35721step1; decide +kernel
      have hl : raw35721step2Labels = raw35721step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35721step2 raw35721step2Labels = mixedMoment B raw35721step3 raw35721step3Labels := by
      have ha : raw35721step3 = raw35721step2 := by apply Matrix.ext; unfold raw35721step3 raw35721step2; decide +kernel
      have hl : raw35721step2Labels = labelEmbedding1 ∘ raw35721step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35721step2 raw35721step2Labels raw35721step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

def raw35722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35722 raw35722Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw35722 raw35722Labels = mixedMoment B raw35722step0 raw35722step0Labels := by
      have hz : ∀ j, raw35722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35722step0 = (fun i j => raw35722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35722step0 raw35722; decide +kernel
      have hl : raw35722step0Labels = raw35722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35722 raw35722Labels permutation346 hz
    mixedMoment B raw35722step0 raw35722step0Labels = mixedMoment B raw35722step1 raw35722step1Labels := by
      have ha : raw35722step1 = (fun i j => raw35722step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35722step1 raw35722step0; decide +kernel
      have hl : raw35722step1Labels = raw35722step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35722step0 raw35722step0Labels permutation127 permutation5
    mixedMoment B raw35722step1 raw35722step1Labels = mixedMoment B raw35722step2 raw35722step2Labels := by
      have ha : raw35722step2 = raw35722step1 := by apply Matrix.ext; unfold raw35722step2 raw35722step1; decide +kernel
      have hl : raw35722step1Labels = labelEmbedding1 ∘ raw35722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35722step1 raw35722step1Labels raw35722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

def raw35723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35723step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35723 raw35723Labels = mixedMoment B node2654 node2654Labels := by
  calc
    mixedMoment B raw35723 raw35723Labels = mixedMoment B raw35723step0 raw35723step0Labels := by
      have ha : raw35723step0 = (fun i j => raw35723 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35723step0 raw35723; decide +kernel
      have hl : raw35723step0Labels = raw35723Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35723 raw35723Labels permutation587 permutation5
    mixedMoment B raw35723step0 raw35723step0Labels = mixedMoment B raw35723step1 raw35723step1Labels := by
      have ha : raw35723step1 = raw35723step0 := by apply Matrix.ext; unfold raw35723step1 raw35723step0; decide +kernel
      have hl : raw35723step0Labels = labelEmbedding1 ∘ raw35723step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35723step0 raw35723step0Labels raw35723step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2654 node2654Labels := by rfl

def raw35724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35724 raw35724Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw35724 raw35724Labels = mixedMoment B raw35724step0 raw35724step0Labels := by
      have hz : ∀ j, raw35724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35724step0 = (fun i j => raw35724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35724step0 raw35724; decide +kernel
      have hl : raw35724step0Labels = raw35724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35724 raw35724Labels permutation346 hz
    mixedMoment B raw35724step0 raw35724step0Labels = mixedMoment B raw35724step1 raw35724step1Labels := by
      have ha : raw35724step1 = (fun i j => raw35724step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35724step1 raw35724step0; decide +kernel
      have hl : raw35724step1Labels = raw35724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35724step0 raw35724step0Labels permutation125 permutation5
    mixedMoment B raw35724step1 raw35724step1Labels = mixedMoment B raw35724step2 raw35724step2Labels := by
      have ha : raw35724step2 = raw35724step1 := by apply Matrix.ext; unfold raw35724step2 raw35724step1; decide +kernel
      have hl : raw35724step1Labels = labelEmbedding1 ∘ raw35724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35724step1 raw35724step1Labels raw35724step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw35725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw35725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw35725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35725 raw35725Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw35725 raw35725Labels = mixedMoment B raw35725step0 raw35725step0Labels := by
      have hz : ∀ j, raw35725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35725step0 = (fun i j => raw35725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35725step0 raw35725; decide +kernel
      have hl : raw35725step0Labels = raw35725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35725 raw35725Labels permutation346 hz
    mixedMoment B raw35725step0 raw35725step0Labels = mixedMoment B raw35725step1 raw35725step1Labels := by
      have ha : raw35725step1 = (fun i j => raw35725step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35725step1 raw35725step0; decide +kernel
      have hl : raw35725step1Labels = raw35725step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35725step0 raw35725step0Labels permutation119 permutation5
    mixedMoment B raw35725step1 raw35725step1Labels = mixedMoment B raw35725step2 raw35725step2Labels := by
      have ha : raw35725step2 = raw35725step1 := by apply Matrix.ext; unfold raw35725step2 raw35725step1; decide +kernel
      have hl : raw35725step1Labels = labelEmbedding1 ∘ raw35725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35725step1 raw35725step1Labels raw35725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw35726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw35726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw35726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35726step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw35726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35726 raw35726Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw35726 raw35726Labels = mixedMoment B raw35726step0 raw35726step0Labels := by
      have hz : ∀ j, raw35726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35726step0 = (fun i j => raw35726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35726step0 raw35726; decide +kernel
      have hl : raw35726step0Labels = raw35726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35726 raw35726Labels permutation346 hz
    mixedMoment B raw35726step0 raw35726step0Labels = mixedMoment B raw35726step1 raw35726step1Labels := by
      have ha : raw35726step1 = (fun i j => raw35726step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35726step1 raw35726step0; decide +kernel
      have hl : raw35726step1Labels = raw35726step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35726step0 raw35726step0Labels permutation33 permutation5
    mixedMoment B raw35726step1 raw35726step1Labels = mixedMoment B raw35726step2 raw35726step2Labels := by
      have ha : raw35726step2 = -raw35726step1 := by apply Matrix.ext; change ∀ i j, raw35726step2 i j = -(raw35726step1 i j); unfold raw35726step2 raw35726step1; decide +kernel
      have hl : raw35726step2Labels = raw35726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35726step2 raw35726step2Labels = mixedMoment B raw35726step3 raw35726step3Labels := by
      have ha : raw35726step3 = raw35726step2 := by apply Matrix.ext; unfold raw35726step3 raw35726step2; decide +kernel
      have hl : raw35726step2Labels = labelEmbedding1 ∘ raw35726step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35726step2 raw35726step2Labels raw35726step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

def raw35727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw35727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw35727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35727 raw35727Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw35727 raw35727Labels = mixedMoment B raw35727step0 raw35727step0Labels := by
      have hz : ∀ j, raw35727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35727step0 = (fun i j => raw35727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35727step0 raw35727; decide +kernel
      have hl : raw35727step0Labels = raw35727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35727 raw35727Labels permutation346 hz
    mixedMoment B raw35727step0 raw35727step0Labels = mixedMoment B raw35727step1 raw35727step1Labels := by
      have ha : raw35727step1 = (fun i j => raw35727step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35727step1 raw35727step0; decide +kernel
      have hl : raw35727step1Labels = raw35727step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35727step0 raw35727step0Labels permutation141 permutation7
    mixedMoment B raw35727step1 raw35727step1Labels = mixedMoment B raw35727step2 raw35727step2Labels := by
      have ha : raw35727step2 = raw35727step1 := by apply Matrix.ext; unfold raw35727step2 raw35727step1; decide +kernel
      have hl : raw35727step1Labels = labelEmbedding1 ∘ raw35727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35727step1 raw35727step1Labels raw35727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

def raw35728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35728 raw35728Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw35728 raw35728Labels = mixedMoment B raw35728step0 raw35728step0Labels := by
      have ha : raw35728step0 = (fun i j => raw35728 (permutation655 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35728step0 raw35728; decide +kernel
      have hl : raw35728step0Labels = raw35728Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35728 raw35728Labels permutation655 permutation7
    mixedMoment B raw35728step0 raw35728step0Labels = mixedMoment B raw35728step1 raw35728step1Labels := by
      have ha : raw35728step1 = raw35728step0 := by apply Matrix.ext; unfold raw35728step1 raw35728step0; decide +kernel
      have hl : raw35728step0Labels = labelEmbedding1 ∘ raw35728step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35728step0 raw35728step0Labels raw35728step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

def raw35729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35729 raw35729Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw35729 raw35729Labels = mixedMoment B raw35729step0 raw35729step0Labels := by
      have hz : ∀ j, raw35729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35729step0 = (fun i j => raw35729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35729step0 raw35729; decide +kernel
      have hl : raw35729step0Labels = raw35729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35729 raw35729Labels permutation346 hz
    mixedMoment B raw35729step0 raw35729step0Labels = mixedMoment B raw35729step1 raw35729step1Labels := by
      have ha : raw35729step1 = (fun i j => raw35729step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35729step1 raw35729step0; decide +kernel
      have hl : raw35729step1Labels = raw35729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35729step0 raw35729step0Labels permutation141 permutation7
    mixedMoment B raw35729step1 raw35729step1Labels = mixedMoment B raw35729step2 raw35729step2Labels := by
      have ha : raw35729step2 = raw35729step1 := by apply Matrix.ext; unfold raw35729step2 raw35729step1; decide +kernel
      have hl : raw35729step1Labels = labelEmbedding1 ∘ raw35729step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35729step1 raw35729step1Labels raw35729step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw35730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw35730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw35730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35730 raw35730Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw35730 raw35730Labels = mixedMoment B raw35730step0 raw35730step0Labels := by
      have hz : ∀ j, raw35730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35730step0 = (fun i j => raw35730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35730step0 raw35730; decide +kernel
      have hl : raw35730step0Labels = raw35730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35730 raw35730Labels permutation346 hz
    mixedMoment B raw35730step0 raw35730step0Labels = mixedMoment B raw35730step1 raw35730step1Labels := by
      have ha : raw35730step1 = (fun i j => raw35730step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35730step1 raw35730step0; decide +kernel
      have hl : raw35730step1Labels = raw35730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35730step0 raw35730step0Labels permutation141 permutation7
    mixedMoment B raw35730step1 raw35730step1Labels = mixedMoment B raw35730step2 raw35730step2Labels := by
      have ha : raw35730step2 = raw35730step1 := by apply Matrix.ext; unfold raw35730step2 raw35730step1; decide +kernel
      have hl : raw35730step1Labels = labelEmbedding1 ∘ raw35730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35730step1 raw35730step1Labels raw35730step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw35731 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35731step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35731step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35731step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35731step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35731 raw35731Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw35731 raw35731Labels = mixedMoment B raw35731step0 raw35731step0Labels := by
      have hz : ∀ j, raw35731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35731step0 = (fun i j => raw35731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35731step0 raw35731; decide +kernel
      have hl : raw35731step0Labels = raw35731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35731 raw35731Labels permutation346 hz
    mixedMoment B raw35731step0 raw35731step0Labels = mixedMoment B raw35731step1 raw35731step1Labels := by
      have ha : raw35731step1 = (fun i j => raw35731step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35731step1 raw35731step0; decide +kernel
      have hl : raw35731step1Labels = raw35731step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35731step0 raw35731step0Labels permutation144 permutation7
    mixedMoment B raw35731step1 raw35731step1Labels = mixedMoment B raw35731step2 raw35731step2Labels := by
      have ha : raw35731step2 = -raw35731step1 := by apply Matrix.ext; change ∀ i j, raw35731step2 i j = -(raw35731step1 i j); unfold raw35731step2 raw35731step1; decide +kernel
      have hl : raw35731step2Labels = raw35731step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35731step2 raw35731step2Labels = mixedMoment B raw35731step3 raw35731step3Labels := by
      have ha : raw35731step3 = raw35731step2 := by apply Matrix.ext; unfold raw35731step3 raw35731step2; decide +kernel
      have hl : raw35731step2Labels = labelEmbedding10 ∘ raw35731step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35731step2 raw35731step2Labels raw35731step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw35732 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35732step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35732step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35732step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35732 raw35732Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw35732 raw35732Labels = mixedMoment B raw35732step0 raw35732step0Labels := by
      have ha : raw35732step0 = (fun i j => raw35732 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35732step0 raw35732; decide +kernel
      have hl : raw35732step0Labels = raw35732Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35732 raw35732Labels permutation267 permutation7
    mixedMoment B raw35732step0 raw35732step0Labels = mixedMoment B raw35732step1 raw35732step1Labels := by
      have ha : raw35732step1 = raw35732step0 := by apply Matrix.ext; unfold raw35732step1 raw35732step0; decide +kernel
      have hl : raw35732step0Labels = labelEmbedding10 ∘ raw35732step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35732step0 raw35732step0Labels raw35732step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw35733 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35733step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35733 raw35733Labels = mixedMoment B node5364 node5364Labels := by
  calc
    mixedMoment B raw35733 raw35733Labels = mixedMoment B raw35733step0 raw35733step0Labels := by
      have hz : ∀ j, raw35733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35733step0 = (fun i j => raw35733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35733step0 raw35733; decide +kernel
      have hl : raw35733step0Labels = raw35733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35733 raw35733Labels permutation346 hz
    mixedMoment B raw35733step0 raw35733step0Labels = mixedMoment B raw35733step1 raw35733step1Labels := by
      have ha : raw35733step1 = (fun i j => raw35733step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35733step1 raw35733step0; decide +kernel
      have hl : raw35733step1Labels = raw35733step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35733step0 raw35733step0Labels permutation144 permutation2
    _ = mixedMoment B node5364 node5364Labels := by rfl

def raw35734 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw35734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw35734step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35734 raw35734Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw35734 raw35734Labels = mixedMoment B raw35734step0 raw35734step0Labels := by
      have hz : ∀ j, raw35734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35734step0 = (fun i j => raw35734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35734step0 raw35734; decide +kernel
      have hl : raw35734step0Labels = raw35734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35734 raw35734Labels permutation346 hz
    mixedMoment B raw35734step0 raw35734step0Labels = mixedMoment B raw35734step1 raw35734step1Labels := by
      have ha : raw35734step1 = (fun i j => raw35734step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35734step1 raw35734step0; decide +kernel
      have hl : raw35734step1Labels = raw35734step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35734step0 raw35734step0Labels permutation144 permutation2
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw35735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 3, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw35735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw35735step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35735 raw35735Labels = mixedMoment B node5195 node5195Labels := by
  calc
    mixedMoment B raw35735 raw35735Labels = mixedMoment B raw35735step0 raw35735step0Labels := by
      have hz : ∀ j, raw35735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35735step0 = (fun i j => raw35735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35735step0 raw35735; decide +kernel
      have hl : raw35735step0Labels = raw35735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35735 raw35735Labels permutation346 hz
    mixedMoment B raw35735step0 raw35735step0Labels = mixedMoment B raw35735step1 raw35735step1Labels := by
      have ha : raw35735step1 = (fun i j => raw35735step0 (permutation68 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35735step1 raw35735step0; decide +kernel
      have hl : raw35735step1Labels = raw35735step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35735step0 raw35735step0Labels permutation68 permutation2
    mixedMoment B raw35735step1 raw35735step1Labels = mixedMoment B raw35735step2 raw35735step2Labels := by
      have ha : raw35735step2 = -raw35735step1 := by apply Matrix.ext; change ∀ i j, raw35735step2 i j = -(raw35735step1 i j); unfold raw35735step2 raw35735step1; decide +kernel
      have hl : raw35735step2Labels = raw35735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5195 node5195Labels := by rfl

def raw35736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw35736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35736step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35736 raw35736Labels = mixedMoment B node5178 node5178Labels := by
  calc
    mixedMoment B raw35736 raw35736Labels = mixedMoment B raw35736step0 raw35736step0Labels := by
      have ha : raw35736step0 = (fun i j => raw35736 (permutation322 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35736step0 raw35736; decide +kernel
      have hl : raw35736step0Labels = raw35736Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35736 raw35736Labels permutation322 permutation2
    mixedMoment B raw35736step0 raw35736step0Labels = mixedMoment B raw35736step1 raw35736step1Labels := by
      have ha : raw35736step1 = -raw35736step0 := by apply Matrix.ext; change ∀ i j, raw35736step1 i j = -(raw35736step0 i j); unfold raw35736step1 raw35736step0; decide +kernel
      have hl : raw35736step1Labels = raw35736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5178 node5178Labels := by rfl

def raw35737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw35737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw35737step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35737 raw35737Labels = mixedMoment B node5180 node5180Labels := by
  calc
    mixedMoment B raw35737 raw35737Labels = mixedMoment B raw35737step0 raw35737step0Labels := by
      have hz : ∀ j, raw35737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35737step0 = (fun i j => raw35737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35737step0 raw35737; decide +kernel
      have hl : raw35737step0Labels = raw35737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35737 raw35737Labels permutation346 hz
    mixedMoment B raw35737step0 raw35737step0Labels = mixedMoment B raw35737step1 raw35737step1Labels := by
      have ha : raw35737step1 = (fun i j => raw35737step0 (permutation68 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35737step1 raw35737step0; decide +kernel
      have hl : raw35737step1Labels = raw35737step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35737step0 raw35737step0Labels permutation68 permutation2
    mixedMoment B raw35737step1 raw35737step1Labels = mixedMoment B raw35737step2 raw35737step2Labels := by
      have ha : raw35737step2 = -raw35737step1 := by apply Matrix.ext; change ∀ i j, raw35737step2 i j = -(raw35737step1 i j); unfold raw35737step2 raw35737step1; decide +kernel
      have hl : raw35737step2Labels = raw35737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5180 node5180Labels := by rfl

def raw35738 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw35738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw35738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw35738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35738 raw35738Labels = mixedMoment B node5084 node5084Labels := by
  calc
    mixedMoment B raw35738 raw35738Labels = mixedMoment B raw35738step0 raw35738step0Labels := by
      have hz : ∀ j, raw35738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35738step0 = (fun i j => raw35738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35738step0 raw35738; decide +kernel
      have hl : raw35738step0Labels = raw35738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35738 raw35738Labels permutation346 hz
    mixedMoment B raw35738step0 raw35738step0Labels = mixedMoment B raw35738step1 raw35738step1Labels := by
      have ha : raw35738step1 = (fun i j => raw35738step0 (permutation141 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35738step1 raw35738step0; decide +kernel
      have hl : raw35738step1Labels = raw35738step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35738step0 raw35738step0Labels permutation141 permutation2
    _ = mixedMoment B node5084 node5084Labels := by rfl

def raw35739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw35739step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35739step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35739step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35739step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35739 raw35739Labels = mixedMoment B node5223 node5223Labels := by
  calc
    mixedMoment B raw35739 raw35739Labels = mixedMoment B raw35739step0 raw35739step0Labels := by
      have ha : raw35739step0 = (fun i j => raw35739 (permutation162 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35739step0 raw35739; decide +kernel
      have hl : raw35739step0Labels = raw35739Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35739 raw35739Labels permutation162 permutation4
    mixedMoment B raw35739step0 raw35739step0Labels = mixedMoment B raw35739step1 raw35739step1Labels := by
      have ha : raw35739step1 = -raw35739step0 := by apply Matrix.ext; change ∀ i j, raw35739step1 i j = -(raw35739step0 i j); unfold raw35739step1 raw35739step0; decide +kernel
      have hl : raw35739step1Labels = raw35739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35739step1 raw35739step1Labels = mixedMoment B raw35739step2 raw35739step2Labels := by
      have ha : raw35739step2 = raw35739step1 := by apply Matrix.ext; unfold raw35739step2 raw35739step1; decide +kernel
      have hl : raw35739step1Labels = labelEmbedding7 ∘ raw35739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35739step1 raw35739step1Labels raw35739step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5223 node5223Labels := by rfl

def raw35740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35740step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35740 raw35740Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw35740 raw35740Labels = mixedMoment B raw35740step0 raw35740step0Labels := by
      have ha : raw35740step0 = (fun i j => raw35740 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35740step0 raw35740; decide +kernel
      have hl : raw35740step0Labels = raw35740Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35740 raw35740Labels permutation152 permutation6
    mixedMoment B raw35740step0 raw35740step0Labels = mixedMoment B raw35740step1 raw35740step1Labels := by
      have ha : raw35740step1 = raw35740step0 := by apply Matrix.ext; unfold raw35740step1 raw35740step0; decide +kernel
      have hl : raw35740step0Labels = labelEmbedding9 ∘ raw35740step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35740step0 raw35740step0Labels raw35740step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw35741 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw35741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35741 raw35741Labels = mixedMoment B node5357 node5357Labels := by
  calc
    mixedMoment B raw35741 raw35741Labels = mixedMoment B raw35741step0 raw35741step0Labels := by
      have ha : raw35741step0 = (fun i j => raw35741 (permutation651 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35741step0 raw35741; decide +kernel
      have hl : raw35741step0Labels = raw35741Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35741 raw35741Labels permutation651 permutation2
    _ = mixedMoment B node5357 node5357Labels := by rfl

def raw35742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw35742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw35742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35742 raw35742Labels = mixedMoment B node5082 node5082Labels := by
  calc
    mixedMoment B raw35742 raw35742Labels = mixedMoment B raw35742step0 raw35742step0Labels := by
      have ha : raw35742step0 = (fun i j => raw35742 (permutation651 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35742step0 raw35742; decide +kernel
      have hl : raw35742step0Labels = raw35742Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35742 raw35742Labels permutation651 permutation2
    _ = mixedMoment B node5082 node5082Labels := by rfl

def raw35743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35743step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35743step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35743step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35743 raw35743Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw35743 raw35743Labels = mixedMoment B raw35743step0 raw35743step0Labels := by
      have hz : ∀ j, raw35743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35743step0 = (fun i j => raw35743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35743step0 raw35743; decide +kernel
      have hl : raw35743step0Labels = raw35743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35743 raw35743Labels permutation346 hz
    mixedMoment B raw35743step0 raw35743step0Labels = mixedMoment B raw35743step1 raw35743step1Labels := by
      have ha : raw35743step1 = (fun i j => raw35743step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35743step1 raw35743step0; decide +kernel
      have hl : raw35743step1Labels = raw35743step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35743step0 raw35743step0Labels permutation36 permutation4
    mixedMoment B raw35743step1 raw35743step1Labels = mixedMoment B raw35743step2 raw35743step2Labels := by
      have ha : raw35743step2 = -raw35743step1 := by apply Matrix.ext; change ∀ i j, raw35743step2 i j = -(raw35743step1 i j); unfold raw35743step2 raw35743step1; decide +kernel
      have hl : raw35743step2Labels = raw35743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35743step2 raw35743step2Labels = mixedMoment B raw35743step3 raw35743step3Labels := by
      have ha : raw35743step3 = raw35743step2 := by apply Matrix.ext; unfold raw35743step3 raw35743step2; decide +kernel
      have hl : raw35743step2Labels = labelEmbedding7 ∘ raw35743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35743step2 raw35743step2Labels raw35743step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw35744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35744step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35744 raw35744Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw35744 raw35744Labels = mixedMoment B raw35744step0 raw35744step0Labels := by
      have hz : ∀ j, raw35744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35744step0 = (fun i j => raw35744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35744step0 raw35744; decide +kernel
      have hl : raw35744step0Labels = raw35744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35744 raw35744Labels permutation346 hz
    mixedMoment B raw35744step0 raw35744step0Labels = mixedMoment B raw35744step1 raw35744step1Labels := by
      have ha : raw35744step1 = (fun i j => raw35744step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35744step1 raw35744step0; decide +kernel
      have hl : raw35744step1Labels = raw35744step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35744step0 raw35744step0Labels permutation32 permutation6
    mixedMoment B raw35744step1 raw35744step1Labels = mixedMoment B raw35744step2 raw35744step2Labels := by
      have ha : raw35744step2 = raw35744step1 := by apply Matrix.ext; unfold raw35744step2 raw35744step1; decide +kernel
      have hl : raw35744step1Labels = labelEmbedding9 ∘ raw35744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35744step1 raw35744step1Labels raw35744step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw35745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35745step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35745 raw35745Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw35745 raw35745Labels = mixedMoment B raw35745step0 raw35745step0Labels := by
      have ha : raw35745step0 = (fun i j => raw35745 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35745step0 raw35745; decide +kernel
      have hl : raw35745step0Labels = raw35745Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35745 raw35745Labels permutation152 permutation6
    mixedMoment B raw35745step0 raw35745step0Labels = mixedMoment B raw35745step1 raw35745step1Labels := by
      have ha : raw35745step1 = raw35745step0 := by apply Matrix.ext; unfold raw35745step1 raw35745step0; decide +kernel
      have hl : raw35745step0Labels = labelEmbedding9 ∘ raw35745step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35745step0 raw35745step0Labels raw35745step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw35746 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw35746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw35746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35746 raw35746Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw35746 raw35746Labels = mixedMoment B raw35746step0 raw35746step0Labels := by
      have hz : ∀ j, raw35746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35746step0 = (fun i j => raw35746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35746step0 raw35746; decide +kernel
      have hl : raw35746step0Labels = raw35746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35746 raw35746Labels permutation346 hz
    mixedMoment B raw35746step0 raw35746step0Labels = mixedMoment B raw35746step1 raw35746step1Labels := by
      have ha : raw35746step1 = (fun i j => raw35746step0 (permutation141 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35746step1 raw35746step0; decide +kernel
      have hl : raw35746step1Labels = raw35746step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35746step0 raw35746step0Labels permutation141 permutation2
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw35747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw35747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw35747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw35747step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw35747step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw35747step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35747 raw35747Labels = mixedMoment B node5225 node5225Labels := by
  calc
    mixedMoment B raw35747 raw35747Labels = mixedMoment B raw35747step0 raw35747step0Labels := by
      have hz : ∀ j, raw35747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35747step0 = (fun i j => raw35747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35747step0 raw35747; decide +kernel
      have hl : raw35747step0Labels = raw35747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35747 raw35747Labels permutation346 hz
    mixedMoment B raw35747step0 raw35747step0Labels = mixedMoment B raw35747step1 raw35747step1Labels := by
      have ha : raw35747step1 = (fun i j => raw35747step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35747step1 raw35747step0; decide +kernel
      have hl : raw35747step1Labels = raw35747step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35747step0 raw35747step0Labels permutation33 permutation4
    mixedMoment B raw35747step1 raw35747step1Labels = mixedMoment B raw35747step2 raw35747step2Labels := by
      have ha : raw35747step2 = -raw35747step1 := by apply Matrix.ext; change ∀ i j, raw35747step2 i j = -(raw35747step1 i j); unfold raw35747step2 raw35747step1; decide +kernel
      have hl : raw35747step2Labels = raw35747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35747step2 raw35747step2Labels = mixedMoment B raw35747step3 raw35747step3Labels := by
      have ha : raw35747step3 = raw35747step2 := by apply Matrix.ext; unfold raw35747step3 raw35747step2; decide +kernel
      have hl : raw35747step2Labels = labelEmbedding7 ∘ raw35747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35747step2 raw35747step2Labels raw35747step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5225 node5225Labels := by rfl

def raw35748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw35748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw35748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35748step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw35748step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35748 raw35748Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw35748 raw35748Labels = mixedMoment B raw35748step0 raw35748step0Labels := by
      have hz : ∀ j, raw35748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35748step0 = (fun i j => raw35748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35748step0 raw35748; decide +kernel
      have hl : raw35748step0Labels = raw35748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35748 raw35748Labels permutation346 hz
    mixedMoment B raw35748step0 raw35748step0Labels = mixedMoment B raw35748step1 raw35748step1Labels := by
      have ha : raw35748step1 = (fun i j => raw35748step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35748step1 raw35748step0; decide +kernel
      have hl : raw35748step1Labels = raw35748step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35748step0 raw35748step0Labels permutation121 permutation5
    mixedMoment B raw35748step1 raw35748step1Labels = mixedMoment B raw35748step2 raw35748step2Labels := by
      have ha : raw35748step2 = raw35748step1 := by apply Matrix.ext; unfold raw35748step2 raw35748step1; decide +kernel
      have hl : raw35748step1Labels = labelEmbedding8 ∘ raw35748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35748step1 raw35748step1Labels raw35748step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw35749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw35749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw35749step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw35749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35749 raw35749Labels = mixedMoment B node5224 node5224Labels := by
  calc
    mixedMoment B raw35749 raw35749Labels = mixedMoment B raw35749step0 raw35749step0Labels := by
      have ha : raw35749step0 = (fun i j => raw35749 (permutation537 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35749step0 raw35749; decide +kernel
      have hl : raw35749step0Labels = raw35749Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35749 raw35749Labels permutation537 permutation5
    mixedMoment B raw35749step0 raw35749step0Labels = mixedMoment B raw35749step1 raw35749step1Labels := by
      have ha : raw35749step1 = raw35749step0 := by apply Matrix.ext; unfold raw35749step1 raw35749step0; decide +kernel
      have hl : raw35749step0Labels = labelEmbedding8 ∘ raw35749step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35749step0 raw35749step0Labels raw35749step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5224 node5224Labels := by rfl

def raw35750 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw35750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw35750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw35750step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw35750step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35750 raw35750Labels = mixedMoment B node5234 node5234Labels := by
  calc
    mixedMoment B raw35750 raw35750Labels = mixedMoment B raw35750step0 raw35750step0Labels := by
      have hz : ∀ j, raw35750 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35750step0 = (fun i j => raw35750 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35750step0 raw35750; decide +kernel
      have hl : raw35750step0Labels = raw35750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35750 raw35750Labels permutation346 hz
    mixedMoment B raw35750step0 raw35750step0Labels = mixedMoment B raw35750step1 raw35750step1Labels := by
      have ha : raw35750step1 = (fun i j => raw35750step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35750step1 raw35750step0; decide +kernel
      have hl : raw35750step1Labels = raw35750step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35750step0 raw35750step0Labels permutation115 permutation5
    mixedMoment B raw35750step1 raw35750step1Labels = mixedMoment B raw35750step2 raw35750step2Labels := by
      have ha : raw35750step2 = raw35750step1 := by apply Matrix.ext; unfold raw35750step2 raw35750step1; decide +kernel
      have hl : raw35750step1Labels = labelEmbedding8 ∘ raw35750step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35750step1 raw35750step1Labels raw35750step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5234 node5234Labels := by rfl

def raw35751 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw35751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw35751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw35751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35751 raw35751Labels = mixedMoment B node5089 node5089Labels := by
  calc
    mixedMoment B raw35751 raw35751Labels = mixedMoment B raw35751step0 raw35751step0Labels := by
      have hz : ∀ j, raw35751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35751step0 = (fun i j => raw35751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35751step0 raw35751; decide +kernel
      have hl : raw35751step0Labels = raw35751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35751 raw35751Labels permutation346 hz
    mixedMoment B raw35751step0 raw35751step0Labels = mixedMoment B raw35751step1 raw35751step1Labels := by
      have ha : raw35751step1 = (fun i j => raw35751step0 (permutation141 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35751step1 raw35751step0; decide +kernel
      have hl : raw35751step1Labels = raw35751step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35751step0 raw35751step0Labels permutation141 permutation2
    _ = mixedMoment B node5089 node5089Labels := by rfl

def raw35752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35752step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35752step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35752step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35752step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35752 raw35752Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw35752 raw35752Labels = mixedMoment B raw35752step0 raw35752step0Labels := by
      have ha : raw35752step0 = (fun i j => raw35752 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35752step0 raw35752; decide +kernel
      have hl : raw35752step0Labels = raw35752Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35752 raw35752Labels permutation289 permutation5
    mixedMoment B raw35752step0 raw35752step0Labels = mixedMoment B raw35752step1 raw35752step1Labels := by
      have ha : raw35752step1 = -raw35752step0 := by apply Matrix.ext; change ∀ i j, raw35752step1 i j = -(raw35752step0 i j); unfold raw35752step1 raw35752step0; decide +kernel
      have hl : raw35752step1Labels = raw35752step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35752step1 raw35752step1Labels = mixedMoment B raw35752step2 raw35752step2Labels := by
      have ha : raw35752step2 = raw35752step1 := by apply Matrix.ext; unfold raw35752step2 raw35752step1; decide +kernel
      have hl : raw35752step1Labels = labelEmbedding8 ∘ raw35752step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35752step1 raw35752step1Labels raw35752step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw35753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35753step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35753step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35753step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35753 raw35753Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw35753 raw35753Labels = mixedMoment B raw35753step0 raw35753step0Labels := by
      have ha : raw35753step0 = (fun i j => raw35753 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35753step0 raw35753; decide +kernel
      have hl : raw35753step0Labels = raw35753Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35753 raw35753Labels permutation289 permutation5
    mixedMoment B raw35753step0 raw35753step0Labels = mixedMoment B raw35753step1 raw35753step1Labels := by
      have ha : raw35753step1 = -raw35753step0 := by apply Matrix.ext; change ∀ i j, raw35753step1 i j = -(raw35753step0 i j); unfold raw35753step1 raw35753step0; decide +kernel
      have hl : raw35753step1Labels = raw35753step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35753step1 raw35753step1Labels = mixedMoment B raw35753step2 raw35753step2Labels := by
      have ha : raw35753step2 = raw35753step1 := by apply Matrix.ext; unfold raw35753step2 raw35753step1; decide +kernel
      have hl : raw35753step1Labels = labelEmbedding8 ∘ raw35753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35753step1 raw35753step1Labels raw35753step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

def raw35754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35754step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35754step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35754step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35754step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35754 raw35754Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw35754 raw35754Labels = mixedMoment B raw35754step0 raw35754step0Labels := by
      have hz : ∀ j, raw35754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35754step0 = (fun i j => raw35754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35754step0 raw35754; decide +kernel
      have hl : raw35754step0Labels = raw35754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35754 raw35754Labels permutation434 hz
    mixedMoment B raw35754step0 raw35754step0Labels = mixedMoment B raw35754step1 raw35754step1Labels := by
      have ha : raw35754step1 = (fun i j => raw35754step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35754step1 raw35754step0; decide +kernel
      have hl : raw35754step1Labels = raw35754step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35754step0 raw35754step0Labels permutation62 permutation5
    mixedMoment B raw35754step1 raw35754step1Labels = mixedMoment B raw35754step2 raw35754step2Labels := by
      have ha : raw35754step2 = -raw35754step1 := by apply Matrix.ext; change ∀ i j, raw35754step2 i j = -(raw35754step1 i j); unfold raw35754step2 raw35754step1; decide +kernel
      have hl : raw35754step2Labels = raw35754step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35754step2 raw35754step2Labels = mixedMoment B raw35754step3 raw35754step3Labels := by
      have ha : raw35754step3 = raw35754step2 := by apply Matrix.ext; unfold raw35754step3 raw35754step2; decide +kernel
      have hl : raw35754step2Labels = labelEmbedding8 ∘ raw35754step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35754step2 raw35754step2Labels raw35754step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw35755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw35755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35755step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35755step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35755step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35755step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35755 raw35755Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw35755 raw35755Labels = mixedMoment B raw35755step0 raw35755step0Labels := by
      have hz : ∀ j, raw35755 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35755step0 = (fun i j => raw35755 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35755step0 raw35755; decide +kernel
      have hl : raw35755step0Labels = raw35755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35755 raw35755Labels permutation520 hz
    mixedMoment B raw35755step0 raw35755step0Labels = mixedMoment B raw35755step1 raw35755step1Labels := by
      have ha : raw35755step1 = (fun i j => raw35755step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35755step1 raw35755step0; decide +kernel
      have hl : raw35755step1Labels = raw35755step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35755step0 raw35755step0Labels permutation62 permutation5
    mixedMoment B raw35755step1 raw35755step1Labels = mixedMoment B raw35755step2 raw35755step2Labels := by
      have ha : raw35755step2 = -raw35755step1 := by apply Matrix.ext; change ∀ i j, raw35755step2 i j = -(raw35755step1 i j); unfold raw35755step2 raw35755step1; decide +kernel
      have hl : raw35755step2Labels = raw35755step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35755step2 raw35755step2Labels = mixedMoment B raw35755step3 raw35755step3Labels := by
      have ha : raw35755step3 = raw35755step2 := by apply Matrix.ext; unfold raw35755step3 raw35755step2; decide +kernel
      have hl : raw35755step2Labels = labelEmbedding8 ∘ raw35755step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35755step2 raw35755step2Labels raw35755step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw35756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35756step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35756 raw35756Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw35756 raw35756Labels = mixedMoment B raw35756step0 raw35756step0Labels := by
      have ha : raw35756step0 = (fun i j => raw35756 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35756step0 raw35756; decide +kernel
      have hl : raw35756step0Labels = raw35756Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35756 raw35756Labels permutation265 permutation3
    mixedMoment B raw35756step0 raw35756step0Labels = mixedMoment B raw35756step1 raw35756step1Labels := by
      have ha : raw35756step1 = raw35756step0 := by apply Matrix.ext; unfold raw35756step1 raw35756step0; decide +kernel
      have hl : raw35756step0Labels = labelEmbedding6 ∘ raw35756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35756step0 raw35756step0Labels raw35756step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw35757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35757 raw35757Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw35757 raw35757Labels = mixedMoment B raw35757step0 raw35757step0Labels := by
      have hz : ∀ j, raw35757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35757step0 = (fun i j => raw35757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35757step0 raw35757; decide +kernel
      have hl : raw35757step0Labels = raw35757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35757 raw35757Labels permutation434 hz
    mixedMoment B raw35757step0 raw35757step0Labels = mixedMoment B raw35757step1 raw35757step1Labels := by
      have ha : raw35757step1 = (fun i j => raw35757step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35757step1 raw35757step0; decide +kernel
      have hl : raw35757step1Labels = raw35757step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35757step0 raw35757step0Labels permutation34 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw35758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw35758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35758 raw35758Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw35758 raw35758Labels = mixedMoment B raw35758step0 raw35758step0Labels := by
      have hz : ∀ j, raw35758 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35758step0 = (fun i j => raw35758 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35758step0 raw35758; decide +kernel
      have hl : raw35758step0Labels = raw35758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35758 raw35758Labels permutation520 hz
    mixedMoment B raw35758step0 raw35758step0Labels = mixedMoment B raw35758step1 raw35758step1Labels := by
      have ha : raw35758step1 = (fun i j => raw35758step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35758step1 raw35758step0; decide +kernel
      have hl : raw35758step1Labels = raw35758step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35758step0 raw35758step0Labels permutation34 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw35759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35759step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35759 raw35759Labels = mixedMoment B node4661 node4661Labels := by
  calc
    mixedMoment B raw35759 raw35759Labels = mixedMoment B raw35759step0 raw35759step0Labels := by
      have ha : raw35759step0 = (fun i j => raw35759 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35759step0 raw35759; decide +kernel
      have hl : raw35759step0Labels = raw35759Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35759 raw35759Labels permutation268 permutation3
    mixedMoment B raw35759step0 raw35759step0Labels = mixedMoment B raw35759step1 raw35759step1Labels := by
      have ha : raw35759step1 = raw35759step0 := by apply Matrix.ext; unfold raw35759step1 raw35759step0; decide +kernel
      have hl : raw35759step0Labels = labelEmbedding6 ∘ raw35759step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35759step0 raw35759step0Labels raw35759step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4661 node4661Labels := by rfl

def raw35760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35760step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35760step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35760step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35760step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35760 raw35760Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw35760 raw35760Labels = mixedMoment B raw35760step0 raw35760step0Labels := by
      have ha : raw35760step0 = (fun i j => raw35760 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35760step0 raw35760; decide +kernel
      have hl : raw35760step0Labels = raw35760Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35760 raw35760Labels permutation518 permutation3
    mixedMoment B raw35760step0 raw35760step0Labels = mixedMoment B raw35760step1 raw35760step1Labels := by
      have ha : raw35760step1 = -raw35760step0 := by apply Matrix.ext; change ∀ i j, raw35760step1 i j = -(raw35760step0 i j); unfold raw35760step1 raw35760step0; decide +kernel
      have hl : raw35760step1Labels = raw35760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35760step1 raw35760step1Labels = mixedMoment B raw35760step2 raw35760step2Labels := by
      have ha : raw35760step2 = raw35760step1 := by apply Matrix.ext; unfold raw35760step2 raw35760step1; decide +kernel
      have hl : raw35760step1Labels = labelEmbedding6 ∘ raw35760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35760step1 raw35760step1Labels raw35760step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

def raw35761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw35761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35761step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35761step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35761step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35761step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35761 raw35761Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35761 raw35761Labels = mixedMoment B raw35761step0 raw35761step0Labels := by
      have hz : ∀ j, raw35761 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35761step0 = (fun i j => raw35761 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35761step0 raw35761; decide +kernel
      have hl : raw35761step0Labels = raw35761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35761 raw35761Labels permutation520 hz
    mixedMoment B raw35761step0 raw35761step0Labels = mixedMoment B raw35761step1 raw35761step1Labels := by
      have ha : raw35761step1 = (fun i j => raw35761step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35761step1 raw35761step0; decide +kernel
      have hl : raw35761step1Labels = raw35761step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35761step0 raw35761step0Labels permutation126 permutation3
    mixedMoment B raw35761step1 raw35761step1Labels = mixedMoment B raw35761step2 raw35761step2Labels := by
      have ha : raw35761step2 = -raw35761step1 := by apply Matrix.ext; change ∀ i j, raw35761step2 i j = -(raw35761step1 i j); unfold raw35761step2 raw35761step1; decide +kernel
      have hl : raw35761step2Labels = raw35761step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35761step2 raw35761step2Labels = mixedMoment B raw35761step3 raw35761step3Labels := by
      have ha : raw35761step3 = raw35761step2 := by apply Matrix.ext; unfold raw35761step3 raw35761step2; decide +kernel
      have hl : raw35761step2Labels = labelEmbedding6 ∘ raw35761step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35761step2 raw35761step2Labels raw35761step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw35762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35762step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35762 raw35762Labels = mixedMoment B node4661 node4661Labels := by
  calc
    mixedMoment B raw35762 raw35762Labels = mixedMoment B raw35762step0 raw35762step0Labels := by
      have ha : raw35762step0 = (fun i j => raw35762 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35762step0 raw35762; decide +kernel
      have hl : raw35762step0Labels = raw35762Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35762 raw35762Labels permutation266 permutation3
    mixedMoment B raw35762step0 raw35762step0Labels = mixedMoment B raw35762step1 raw35762step1Labels := by
      have ha : raw35762step1 = raw35762step0 := by apply Matrix.ext; unfold raw35762step1 raw35762step0; decide +kernel
      have hl : raw35762step0Labels = labelEmbedding6 ∘ raw35762step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35762step0 raw35762step0Labels raw35762step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4661 node4661Labels := by rfl

def raw35763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35763 raw35763Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw35763 raw35763Labels = mixedMoment B raw35763step0 raw35763step0Labels := by
      have ha : raw35763step0 = (fun i j => raw35763 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35763step0 raw35763; decide +kernel
      have hl : raw35763step0Labels = raw35763Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35763 raw35763Labels permutation588 permutation3
    mixedMoment B raw35763step0 raw35763step0Labels = mixedMoment B raw35763step1 raw35763step1Labels := by
      have ha : raw35763step1 = -raw35763step0 := by apply Matrix.ext; change ∀ i j, raw35763step1 i j = -(raw35763step0 i j); unfold raw35763step1 raw35763step0; decide +kernel
      have hl : raw35763step1Labels = raw35763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35763step1 raw35763step1Labels = mixedMoment B raw35763step2 raw35763step2Labels := by
      have ha : raw35763step2 = raw35763step1 := by apply Matrix.ext; unfold raw35763step2 raw35763step1; decide +kernel
      have hl : raw35763step1Labels = labelEmbedding6 ∘ raw35763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35763step1 raw35763step1Labels raw35763step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

def raw35764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35764step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35764step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35764step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35764 raw35764Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35764 raw35764Labels = mixedMoment B raw35764step0 raw35764step0Labels := by
      have hz : ∀ j, raw35764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35764step0 = (fun i j => raw35764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35764step0 raw35764; decide +kernel
      have hl : raw35764step0Labels = raw35764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35764 raw35764Labels permutation434 hz
    mixedMoment B raw35764step0 raw35764step0Labels = mixedMoment B raw35764step1 raw35764step1Labels := by
      have ha : raw35764step1 = (fun i j => raw35764step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35764step1 raw35764step0; decide +kernel
      have hl : raw35764step1Labels = raw35764step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35764step0 raw35764step0Labels permutation126 permutation3
    mixedMoment B raw35764step1 raw35764step1Labels = mixedMoment B raw35764step2 raw35764step2Labels := by
      have ha : raw35764step2 = -raw35764step1 := by apply Matrix.ext; change ∀ i j, raw35764step2 i j = -(raw35764step1 i j); unfold raw35764step2 raw35764step1; decide +kernel
      have hl : raw35764step2Labels = raw35764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35764step2 raw35764step2Labels = mixedMoment B raw35764step3 raw35764step3Labels := by
      have ha : raw35764step3 = raw35764step2 := by apply Matrix.ext; unfold raw35764step3 raw35764step2; decide +kernel
      have hl : raw35764step2Labels = labelEmbedding6 ∘ raw35764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35764step2 raw35764step2Labels raw35764step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw35765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw35765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw35765step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw35765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35765 raw35765Labels = mixedMoment B node4660 node4660Labels := by
  calc
    mixedMoment B raw35765 raw35765Labels = mixedMoment B raw35765step0 raw35765step0Labels := by
      have ha : raw35765step0 = (fun i j => raw35765 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35765step0 raw35765; decide +kernel
      have hl : raw35765step0Labels = raw35765Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35765 raw35765Labels permutation265 permutation3
    mixedMoment B raw35765step0 raw35765step0Labels = mixedMoment B raw35765step1 raw35765step1Labels := by
      have ha : raw35765step1 = raw35765step0 := by apply Matrix.ext; unfold raw35765step1 raw35765step0; decide +kernel
      have hl : raw35765step0Labels = labelEmbedding6 ∘ raw35765step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35765step0 raw35765step0Labels raw35765step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4660 node4660Labels := by rfl

def raw35766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw35766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35766step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35766step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35766step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35766 raw35766Labels = mixedMoment B node5030 node5030Labels := by
  calc
    mixedMoment B raw35766 raw35766Labels = mixedMoment B raw35766step0 raw35766step0Labels := by
      have ha : raw35766step0 = (fun i j => raw35766 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35766step0 raw35766; decide +kernel
      have hl : raw35766step0Labels = raw35766Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35766 raw35766Labels permutation663 permutation3
    mixedMoment B raw35766step0 raw35766step0Labels = mixedMoment B raw35766step1 raw35766step1Labels := by
      have ha : raw35766step1 = -raw35766step0 := by apply Matrix.ext; change ∀ i j, raw35766step1 i j = -(raw35766step0 i j); unfold raw35766step1 raw35766step0; decide +kernel
      have hl : raw35766step1Labels = raw35766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35766step1 raw35766step1Labels = mixedMoment B raw35766step2 raw35766step2Labels := by
      have ha : raw35766step2 = raw35766step1 := by apply Matrix.ext; unfold raw35766step2 raw35766step1; decide +kernel
      have hl : raw35766step1Labels = labelEmbedding6 ∘ raw35766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35766step1 raw35766step1Labels raw35766step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5030 node5030Labels := by rfl

def raw35767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw35767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw35767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35767step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35767 raw35767Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw35767 raw35767Labels = mixedMoment B raw35767step0 raw35767step0Labels := by
      have hz : ∀ j, raw35767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35767step0 = (fun i j => raw35767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35767step0 raw35767; decide +kernel
      have hl : raw35767step0Labels = raw35767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35767 raw35767Labels permutation434 hz
    mixedMoment B raw35767step0 raw35767step0Labels = mixedMoment B raw35767step1 raw35767step1Labels := by
      have ha : raw35767step1 = (fun i j => raw35767step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35767step1 raw35767step0; decide +kernel
      have hl : raw35767step1Labels = raw35767step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35767step0 raw35767step0Labels permutation150 permutation3
    mixedMoment B raw35767step1 raw35767step1Labels = mixedMoment B raw35767step2 raw35767step2Labels := by
      have ha : raw35767step2 = -raw35767step1 := by apply Matrix.ext; change ∀ i j, raw35767step2 i j = -(raw35767step1 i j); unfold raw35767step2 raw35767step1; decide +kernel
      have hl : raw35767step2Labels = raw35767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35767step2 raw35767step2Labels = mixedMoment B raw35767step3 raw35767step3Labels := by
      have ha : raw35767step3 = raw35767step2 := by apply Matrix.ext; unfold raw35767step3 raw35767step2; decide +kernel
      have hl : raw35767step2Labels = labelEmbedding6 ∘ raw35767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35767step2 raw35767step2Labels raw35767step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw35768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw35768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw35768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35768step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35768step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35768step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35768 raw35768Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw35768 raw35768Labels = mixedMoment B raw35768step0 raw35768step0Labels := by
      have hz : ∀ j, raw35768 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35768step0 = (fun i j => raw35768 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35768step0 raw35768; decide +kernel
      have hl : raw35768step0Labels = raw35768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35768 raw35768Labels permutation520 hz
    mixedMoment B raw35768step0 raw35768step0Labels = mixedMoment B raw35768step1 raw35768step1Labels := by
      have ha : raw35768step1 = (fun i j => raw35768step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35768step1 raw35768step0; decide +kernel
      have hl : raw35768step1Labels = raw35768step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35768step0 raw35768step0Labels permutation150 permutation3
    mixedMoment B raw35768step1 raw35768step1Labels = mixedMoment B raw35768step2 raw35768step2Labels := by
      have ha : raw35768step2 = -raw35768step1 := by apply Matrix.ext; change ∀ i j, raw35768step2 i j = -(raw35768step1 i j); unfold raw35768step2 raw35768step1; decide +kernel
      have hl : raw35768step2Labels = raw35768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35768step2 raw35768step2Labels = mixedMoment B raw35768step3 raw35768step3Labels := by
      have ha : raw35768step3 = raw35768step2 := by apply Matrix.ext; unfold raw35768step3 raw35768step2; decide +kernel
      have hl : raw35768step2Labels = labelEmbedding6 ∘ raw35768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35768step2 raw35768step2Labels raw35768step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw35769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35769 raw35769Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw35769 raw35769Labels = mixedMoment B raw35769step0 raw35769step0Labels := by
      have ha : raw35769step0 = (fun i j => raw35769 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35769step0 raw35769; decide +kernel
      have hl : raw35769step0Labels = raw35769Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35769 raw35769Labels permutation265 permutation2
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw35770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35770 raw35770Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw35770 raw35770Labels = mixedMoment B raw35770step0 raw35770step0Labels := by
      have ha : raw35770step0 = (fun i j => raw35770 (permutation289 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35770step0 raw35770; decide +kernel
      have hl : raw35770step0Labels = raw35770Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35770 raw35770Labels permutation289 permutation2
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw35771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35771 raw35771Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw35771 raw35771Labels = mixedMoment B raw35771step0 raw35771step0Labels := by
      have ha : raw35771step0 = (fun i j => raw35771 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35771step0 raw35771; decide +kernel
      have hl : raw35771step0Labels = raw35771Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35771 raw35771Labels permutation265 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw35772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35772 raw35772Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw35772 raw35772Labels = mixedMoment B raw35772step0 raw35772step0Labels := by
      have ha : raw35772step0 = (fun i j => raw35772 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35772step0 raw35772; decide +kernel
      have hl : raw35772step0Labels = raw35772Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35772 raw35772Labels permutation267 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw35773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw35773step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw35773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35773 raw35773Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw35773 raw35773Labels = mixedMoment B raw35773step0 raw35773step0Labels := by
      have ha : raw35773step0 = (fun i j => raw35773 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35773step0 raw35773; decide +kernel
      have hl : raw35773step0Labels = raw35773Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35773 raw35773Labels permutation152 permutation3
    mixedMoment B raw35773step0 raw35773step0Labels = mixedMoment B raw35773step1 raw35773step1Labels := by
      have ha : raw35773step1 = raw35773step0 := by apply Matrix.ext; unfold raw35773step1 raw35773step0; decide +kernel
      have hl : raw35773step0Labels = labelEmbedding6 ∘ raw35773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35773step0 raw35773step0Labels raw35773step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw35774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35774step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35774 raw35774Labels = mixedMoment B node4677 node4677Labels := by
  calc
    mixedMoment B raw35774 raw35774Labels = mixedMoment B raw35774step0 raw35774step0Labels := by
      have ha : raw35774step0 = (fun i j => raw35774 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35774step0 raw35774; decide +kernel
      have hl : raw35774step0Labels = raw35774Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35774 raw35774Labels permutation160 permutation3
    mixedMoment B raw35774step0 raw35774step0Labels = mixedMoment B raw35774step1 raw35774step1Labels := by
      have ha : raw35774step1 = raw35774step0 := by apply Matrix.ext; unfold raw35774step1 raw35774step0; decide +kernel
      have hl : raw35774step0Labels = labelEmbedding6 ∘ raw35774step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35774step0 raw35774step0Labels raw35774step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4677 node4677Labels := by rfl

def raw35775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35775 raw35775Labels = mixedMoment B node4964 node4964Labels := by
  calc
    mixedMoment B raw35775 raw35775Labels = mixedMoment B raw35775step0 raw35775step0Labels := by
      have ha : raw35775step0 = (fun i j => raw35775 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35775step0 raw35775; decide +kernel
      have hl : raw35775step0Labels = raw35775Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35775 raw35775Labels permutation265 permutation2
    _ = mixedMoment B node4964 node4964Labels := by rfl

def raw35776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35776step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35776 raw35776Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw35776 raw35776Labels = mixedMoment B raw35776step0 raw35776step0Labels := by
      have ha : raw35776step0 = (fun i j => raw35776 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35776step0 raw35776; decide +kernel
      have hl : raw35776step0Labels = raw35776Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35776 raw35776Labels permutation160 permutation3
    mixedMoment B raw35776step0 raw35776step0Labels = mixedMoment B raw35776step1 raw35776step1Labels := by
      have ha : raw35776step1 = raw35776step0 := by apply Matrix.ext; unfold raw35776step1 raw35776step0; decide +kernel
      have hl : raw35776step0Labels = labelEmbedding6 ∘ raw35776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35776step0 raw35776step0Labels raw35776step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw35777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35777step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35777step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35777 raw35777Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw35777 raw35777Labels = mixedMoment B raw35777step0 raw35777step0Labels := by
      have ha : raw35777step0 = (fun i j => raw35777 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35777step0 raw35777; decide +kernel
      have hl : raw35777step0Labels = raw35777Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35777 raw35777Labels permutation166 permutation3
    mixedMoment B raw35777step0 raw35777step0Labels = mixedMoment B raw35777step1 raw35777step1Labels := by
      have ha : raw35777step1 = raw35777step0 := by apply Matrix.ext; unfold raw35777step1 raw35777step0; decide +kernel
      have hl : raw35777step0Labels = labelEmbedding6 ∘ raw35777step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35777step0 raw35777step0Labels raw35777step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw35778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35778step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35778 raw35778Labels = mixedMoment B node4666 node4666Labels := by
  calc
    mixedMoment B raw35778 raw35778Labels = mixedMoment B raw35778step0 raw35778step0Labels := by
      have ha : raw35778step0 = (fun i j => raw35778 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35778step0 raw35778; decide +kernel
      have hl : raw35778step0Labels = raw35778Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35778 raw35778Labels permutation154 permutation3
    mixedMoment B raw35778step0 raw35778step0Labels = mixedMoment B raw35778step1 raw35778step1Labels := by
      have ha : raw35778step1 = raw35778step0 := by apply Matrix.ext; unfold raw35778step1 raw35778step0; decide +kernel
      have hl : raw35778step0Labels = labelEmbedding6 ∘ raw35778step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35778step0 raw35778step0Labels raw35778step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4666 node4666Labels := by rfl

def raw35779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35779 raw35779Labels = mixedMoment B node4958 node4958Labels := by
  calc
    mixedMoment B raw35779 raw35779Labels = mixedMoment B raw35779step0 raw35779step0Labels := by
      have ha : raw35779step0 = (fun i j => raw35779 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35779step0 raw35779; decide +kernel
      have hl : raw35779step0Labels = raw35779Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35779 raw35779Labels permutation267 permutation2
    _ = mixedMoment B node4958 node4958Labels := by rfl

def raw35780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35780 raw35780Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw35780 raw35780Labels = mixedMoment B raw35780step0 raw35780step0Labels := by
      have ha : raw35780step0 = (fun i j => raw35780 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35780step0 raw35780; decide +kernel
      have hl : raw35780step0Labels = raw35780Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35780 raw35780Labels permutation267 permutation2
    _ = mixedMoment B node5373 node5373Labels := by rfl

def raw35781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35781 raw35781Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw35781 raw35781Labels = mixedMoment B raw35781step0 raw35781step0Labels := by
      have ha : raw35781step0 = (fun i j => raw35781 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35781step0 raw35781; decide +kernel
      have hl : raw35781step0Labels = raw35781Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35781 raw35781Labels permutation267 permutation2
    _ = mixedMoment B node5377 node5377Labels := by rfl

def raw35782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35782step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35782step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35782 raw35782Labels = mixedMoment B node4666 node4666Labels := by
  calc
    mixedMoment B raw35782 raw35782Labels = mixedMoment B raw35782step0 raw35782step0Labels := by
      have ha : raw35782step0 = (fun i j => raw35782 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35782step0 raw35782; decide +kernel
      have hl : raw35782step0Labels = raw35782Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35782 raw35782Labels permutation152 permutation3
    mixedMoment B raw35782step0 raw35782step0Labels = mixedMoment B raw35782step1 raw35782step1Labels := by
      have ha : raw35782step1 = raw35782step0 := by apply Matrix.ext; unfold raw35782step1 raw35782step0; decide +kernel
      have hl : raw35782step0Labels = labelEmbedding6 ∘ raw35782step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35782step0 raw35782step0Labels raw35782step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4666 node4666Labels := by rfl

def raw35783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35783 raw35783Labels = mixedMoment B node4958 node4958Labels := by
  calc
    mixedMoment B raw35783 raw35783Labels = mixedMoment B raw35783step0 raw35783step0Labels := by
      have ha : raw35783step0 = (fun i j => raw35783 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35783step0 raw35783; decide +kernel
      have hl : raw35783step0Labels = raw35783Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35783 raw35783Labels permutation265 permutation2
    _ = mixedMoment B node4958 node4958Labels := by rfl

def raw35784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35784 raw35784Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw35784 raw35784Labels = mixedMoment B raw35784step0 raw35784step0Labels := by
      have ha : raw35784step0 = (fun i j => raw35784 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35784step0 raw35784; decide +kernel
      have hl : raw35784step0Labels = raw35784Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35784 raw35784Labels permutation265 permutation2
    _ = mixedMoment B node5373 node5373Labels := by rfl

def raw35785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35785 raw35785Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw35785 raw35785Labels = mixedMoment B raw35785step0 raw35785step0Labels := by
      have ha : raw35785step0 = (fun i j => raw35785 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35785step0 raw35785; decide +kernel
      have hl : raw35785step0Labels = raw35785Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35785 raw35785Labels permutation265 permutation2
    _ = mixedMoment B node5377 node5377Labels := by rfl

def raw35786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35786step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35786 raw35786Labels = mixedMoment B node4663 node4663Labels := by
  calc
    mixedMoment B raw35786 raw35786Labels = mixedMoment B raw35786step0 raw35786step0Labels := by
      have ha : raw35786step0 = (fun i j => raw35786 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35786step0 raw35786; decide +kernel
      have hl : raw35786step0Labels = raw35786Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35786 raw35786Labels permutation152 permutation3
    mixedMoment B raw35786step0 raw35786step0Labels = mixedMoment B raw35786step1 raw35786step1Labels := by
      have ha : raw35786step1 = raw35786step0 := by apply Matrix.ext; unfold raw35786step1 raw35786step0; decide +kernel
      have hl : raw35786step0Labels = labelEmbedding6 ∘ raw35786step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35786step0 raw35786step0Labels raw35786step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4663 node4663Labels := by rfl

def raw35787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35787 raw35787Labels = mixedMoment B node4956 node4956Labels := by
  calc
    mixedMoment B raw35787 raw35787Labels = mixedMoment B raw35787step0 raw35787step0Labels := by
      have ha : raw35787step0 = (fun i j => raw35787 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35787step0 raw35787; decide +kernel
      have hl : raw35787step0Labels = raw35787Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35787 raw35787Labels permutation265 permutation2
    _ = mixedMoment B node4956 node4956Labels := by rfl

def raw35788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35788step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35788step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35788step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35788 raw35788Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw35788 raw35788Labels = mixedMoment B raw35788step0 raw35788step0Labels := by
      have ha : raw35788step0 = (fun i j => raw35788 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35788step0 raw35788; decide +kernel
      have hl : raw35788step0Labels = raw35788Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35788 raw35788Labels permutation664 permutation3
    mixedMoment B raw35788step0 raw35788step0Labels = mixedMoment B raw35788step1 raw35788step1Labels := by
      have ha : raw35788step1 = -raw35788step0 := by apply Matrix.ext; change ∀ i j, raw35788step1 i j = -(raw35788step0 i j); unfold raw35788step1 raw35788step0; decide +kernel
      have hl : raw35788step1Labels = raw35788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35788step1 raw35788step1Labels = mixedMoment B raw35788step2 raw35788step2Labels := by
      have ha : raw35788step2 = raw35788step1 := by apply Matrix.ext; unfold raw35788step2 raw35788step1; decide +kernel
      have hl : raw35788step1Labels = labelEmbedding6 ∘ raw35788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35788step1 raw35788step1Labels raw35788step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5114 node5114Labels := by rfl

def raw35789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35789step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35789step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35789step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35789 raw35789Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw35789 raw35789Labels = mixedMoment B raw35789step0 raw35789step0Labels := by
      have ha : raw35789step0 = (fun i j => raw35789 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35789step0 raw35789; decide +kernel
      have hl : raw35789step0Labels = raw35789Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35789 raw35789Labels permutation682 permutation3
    mixedMoment B raw35789step0 raw35789step0Labels = mixedMoment B raw35789step1 raw35789step1Labels := by
      have ha : raw35789step1 = -raw35789step0 := by apply Matrix.ext; change ∀ i j, raw35789step1 i j = -(raw35789step0 i j); unfold raw35789step1 raw35789step0; decide +kernel
      have hl : raw35789step1Labels = raw35789step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35789step1 raw35789step1Labels = mixedMoment B raw35789step2 raw35789step2Labels := by
      have ha : raw35789step2 = raw35789step1 := by apply Matrix.ext; unfold raw35789step2 raw35789step1; decide +kernel
      have hl : raw35789step1Labels = labelEmbedding6 ∘ raw35789step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35789step1 raw35789step1Labels raw35789step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw35790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw35790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35790step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35790step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35790step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35790step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35790 raw35790Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw35790 raw35790Labels = mixedMoment B raw35790step0 raw35790step0Labels := by
      have ha : raw35790step0 = (fun i j => raw35790 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35790step0 raw35790; decide +kernel
      have hl : raw35790step0Labels = raw35790Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35790 raw35790Labels permutation658 permutation3
    mixedMoment B raw35790step0 raw35790step0Labels = mixedMoment B raw35790step1 raw35790step1Labels := by
      have ha : raw35790step1 = -raw35790step0 := by apply Matrix.ext; change ∀ i j, raw35790step1 i j = -(raw35790step0 i j); unfold raw35790step1 raw35790step0; decide +kernel
      have hl : raw35790step1Labels = raw35790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35790step1 raw35790step1Labels = mixedMoment B raw35790step2 raw35790step2Labels := by
      have ha : raw35790step2 = raw35790step1 := by apply Matrix.ext; unfold raw35790step2 raw35790step1; decide +kernel
      have hl : raw35790step1Labels = labelEmbedding6 ∘ raw35790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35790step1 raw35790step1Labels raw35790step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw35791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35791step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35791step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35791 raw35791Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw35791 raw35791Labels = mixedMoment B raw35791step0 raw35791step0Labels := by
      have ha : raw35791step0 = (fun i j => raw35791 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35791step0 raw35791; decide +kernel
      have hl : raw35791step0Labels = raw35791Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35791 raw35791Labels permutation289 permutation7
    mixedMoment B raw35791step0 raw35791step0Labels = mixedMoment B raw35791step1 raw35791step1Labels := by
      have ha : raw35791step1 = -raw35791step0 := by apply Matrix.ext; change ∀ i j, raw35791step1 i j = -(raw35791step0 i j); unfold raw35791step1 raw35791step0; decide +kernel
      have hl : raw35791step1Labels = raw35791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35791step1 raw35791step1Labels = mixedMoment B raw35791step2 raw35791step2Labels := by
      have ha : raw35791step2 = raw35791step1 := by apply Matrix.ext; unfold raw35791step2 raw35791step1; decide +kernel
      have hl : raw35791step1Labels = labelEmbedding1 ∘ raw35791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35791step1 raw35791step1Labels raw35791step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw35792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35792step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35792step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35792 raw35792Labels = mixedMoment B node3798 node3798Labels := by
  calc
    mixedMoment B raw35792 raw35792Labels = mixedMoment B raw35792step0 raw35792step0Labels := by
      have ha : raw35792step0 = (fun i j => raw35792 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35792step0 raw35792; decide +kernel
      have hl : raw35792step0Labels = raw35792Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35792 raw35792Labels permutation289 permutation7
    mixedMoment B raw35792step0 raw35792step0Labels = mixedMoment B raw35792step1 raw35792step1Labels := by
      have ha : raw35792step1 = -raw35792step0 := by apply Matrix.ext; change ∀ i j, raw35792step1 i j = -(raw35792step0 i j); unfold raw35792step1 raw35792step0; decide +kernel
      have hl : raw35792step1Labels = raw35792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35792step1 raw35792step1Labels = mixedMoment B raw35792step2 raw35792step2Labels := by
      have ha : raw35792step2 = raw35792step1 := by apply Matrix.ext; unfold raw35792step2 raw35792step1; decide +kernel
      have hl : raw35792step1Labels = labelEmbedding1 ∘ raw35792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35792step1 raw35792step1Labels raw35792step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3798 node3798Labels := by rfl

def raw35793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35793 raw35793Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw35793 raw35793Labels = mixedMoment B raw35793step0 raw35793step0Labels := by
      have ha : raw35793step0 = (fun i j => raw35793 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35793step0 raw35793; decide +kernel
      have hl : raw35793step0Labels = raw35793Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35793 raw35793Labels permutation289 permutation7
    mixedMoment B raw35793step0 raw35793step0Labels = mixedMoment B raw35793step1 raw35793step1Labels := by
      have ha : raw35793step1 = -raw35793step0 := by apply Matrix.ext; change ∀ i j, raw35793step1 i j = -(raw35793step0 i j); unfold raw35793step1 raw35793step0; decide +kernel
      have hl : raw35793step1Labels = raw35793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35793step1 raw35793step1Labels = mixedMoment B raw35793step2 raw35793step2Labels := by
      have ha : raw35793step2 = raw35793step1 := by apply Matrix.ext; unfold raw35793step2 raw35793step1; decide +kernel
      have hl : raw35793step1Labels = labelEmbedding1 ∘ raw35793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35793step1 raw35793step1Labels raw35793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw35794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35794step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35794step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35794 raw35794Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw35794 raw35794Labels = mixedMoment B raw35794step0 raw35794step0Labels := by
      have ha : raw35794step0 = (fun i j => raw35794 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35794step0 raw35794; decide +kernel
      have hl : raw35794step0Labels = raw35794Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35794 raw35794Labels permutation291 permutation7
    mixedMoment B raw35794step0 raw35794step0Labels = mixedMoment B raw35794step1 raw35794step1Labels := by
      have ha : raw35794step1 = -raw35794step0 := by apply Matrix.ext; change ∀ i j, raw35794step1 i j = -(raw35794step0 i j); unfold raw35794step1 raw35794step0; decide +kernel
      have hl : raw35794step1Labels = raw35794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35794step1 raw35794step1Labels = mixedMoment B raw35794step2 raw35794step2Labels := by
      have ha : raw35794step2 = raw35794step1 := by apply Matrix.ext; unfold raw35794step2 raw35794step1; decide +kernel
      have hl : raw35794step1Labels = labelEmbedding1 ∘ raw35794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35794step1 raw35794step1Labels raw35794step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw35795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35795step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35795step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35795 raw35795Labels = mixedMoment B node3844 node3844Labels := by
  calc
    mixedMoment B raw35795 raw35795Labels = mixedMoment B raw35795step0 raw35795step0Labels := by
      have ha : raw35795step0 = (fun i j => raw35795 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35795step0 raw35795; decide +kernel
      have hl : raw35795step0Labels = raw35795Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35795 raw35795Labels permutation289 permutation7
    mixedMoment B raw35795step0 raw35795step0Labels = mixedMoment B raw35795step1 raw35795step1Labels := by
      have ha : raw35795step1 = -raw35795step0 := by apply Matrix.ext; change ∀ i j, raw35795step1 i j = -(raw35795step0 i j); unfold raw35795step1 raw35795step0; decide +kernel
      have hl : raw35795step1Labels = raw35795step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35795step1 raw35795step1Labels = mixedMoment B raw35795step2 raw35795step2Labels := by
      have ha : raw35795step2 = raw35795step1 := by apply Matrix.ext; unfold raw35795step2 raw35795step1; decide +kernel
      have hl : raw35795step1Labels = labelEmbedding1 ∘ raw35795step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35795step1 raw35795step1Labels raw35795step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3844 node3844Labels := by rfl

def raw35796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw35796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35796step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35796 raw35796Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw35796 raw35796Labels = mixedMoment B raw35796step0 raw35796step0Labels := by
      have ha : raw35796step0 = (fun i j => raw35796 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35796step0 raw35796; decide +kernel
      have hl : raw35796step0Labels = raw35796Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35796 raw35796Labels permutation212 permutation5
    mixedMoment B raw35796step0 raw35796step0Labels = mixedMoment B raw35796step1 raw35796step1Labels := by
      have ha : raw35796step1 = -raw35796step0 := by apply Matrix.ext; change ∀ i j, raw35796step1 i j = -(raw35796step0 i j); unfold raw35796step1 raw35796step0; decide +kernel
      have hl : raw35796step1Labels = raw35796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35796step1 raw35796step1Labels = mixedMoment B raw35796step2 raw35796step2Labels := by
      have ha : raw35796step2 = raw35796step1 := by apply Matrix.ext; unfold raw35796step2 raw35796step1; decide +kernel
      have hl : raw35796step1Labels = labelEmbedding1 ∘ raw35796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35796step1 raw35796step1Labels raw35796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw35797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw35797step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35797step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35797 raw35797Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw35797 raw35797Labels = mixedMoment B raw35797step0 raw35797step0Labels := by
      have ha : raw35797step0 = (fun i j => raw35797 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35797step0 raw35797; decide +kernel
      have hl : raw35797step0Labels = raw35797Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35797 raw35797Labels permutation184 permutation5
    mixedMoment B raw35797step0 raw35797step0Labels = mixedMoment B raw35797step1 raw35797step1Labels := by
      have ha : raw35797step1 = -raw35797step0 := by apply Matrix.ext; change ∀ i j, raw35797step1 i j = -(raw35797step0 i j); unfold raw35797step1 raw35797step0; decide +kernel
      have hl : raw35797step1Labels = raw35797step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35797step1 raw35797step1Labels = mixedMoment B raw35797step2 raw35797step2Labels := by
      have ha : raw35797step2 = raw35797step1 := by apply Matrix.ext; unfold raw35797step2 raw35797step1; decide +kernel
      have hl : raw35797step1Labels = labelEmbedding1 ∘ raw35797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35797step1 raw35797step1Labels raw35797step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3900 node3900Labels := by rfl

def raw35798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw35798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35798step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35798 raw35798Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw35798 raw35798Labels = mixedMoment B raw35798step0 raw35798step0Labels := by
      have ha : raw35798step0 = (fun i j => raw35798 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35798step0 raw35798; decide +kernel
      have hl : raw35798step0Labels = raw35798Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35798 raw35798Labels permutation212 permutation5
    mixedMoment B raw35798step0 raw35798step0Labels = mixedMoment B raw35798step1 raw35798step1Labels := by
      have ha : raw35798step1 = -raw35798step0 := by apply Matrix.ext; change ∀ i j, raw35798step1 i j = -(raw35798step0 i j); unfold raw35798step1 raw35798step0; decide +kernel
      have hl : raw35798step1Labels = raw35798step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35798step1 raw35798step1Labels = mixedMoment B raw35798step2 raw35798step2Labels := by
      have ha : raw35798step2 = raw35798step1 := by apply Matrix.ext; unfold raw35798step2 raw35798step1; decide +kernel
      have hl : raw35798step1Labels = labelEmbedding1 ∘ raw35798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35798step1 raw35798step1Labels raw35798step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw35799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw35799step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35799step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35799 raw35799Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw35799 raw35799Labels = mixedMoment B raw35799step0 raw35799step0Labels := by
      have ha : raw35799step0 = (fun i j => raw35799 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35799step0 raw35799; decide +kernel
      have hl : raw35799step0Labels = raw35799Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35799 raw35799Labels permutation234 permutation5
    mixedMoment B raw35799step0 raw35799step0Labels = mixedMoment B raw35799step1 raw35799step1Labels := by
      have ha : raw35799step1 = -raw35799step0 := by apply Matrix.ext; change ∀ i j, raw35799step1 i j = -(raw35799step0 i j); unfold raw35799step1 raw35799step0; decide +kernel
      have hl : raw35799step1Labels = raw35799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35799step1 raw35799step1Labels = mixedMoment B raw35799step2 raw35799step2Labels := by
      have ha : raw35799step2 = raw35799step1 := by apply Matrix.ext; unfold raw35799step2 raw35799step1; decide +kernel
      have hl : raw35799step1Labels = labelEmbedding1 ∘ raw35799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35799step1 raw35799step1Labels raw35799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw35800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw35800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw35800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35800step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw35800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35800 raw35800Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw35800 raw35800Labels = mixedMoment B raw35800step0 raw35800step0Labels := by
      have ha : raw35800step0 = (fun i j => raw35800 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35800step0 raw35800; decide +kernel
      have hl : raw35800step0Labels = raw35800Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35800 raw35800Labels permutation216 permutation5
    mixedMoment B raw35800step0 raw35800step0Labels = mixedMoment B raw35800step1 raw35800step1Labels := by
      have ha : raw35800step1 = -raw35800step0 := by apply Matrix.ext; change ∀ i j, raw35800step1 i j = -(raw35800step0 i j); unfold raw35800step1 raw35800step0; decide +kernel
      have hl : raw35800step1Labels = raw35800step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35800step1 raw35800step1Labels = mixedMoment B raw35800step2 raw35800step2Labels := by
      have ha : raw35800step2 = raw35800step1 := by apply Matrix.ext; unfold raw35800step2 raw35800step1; decide +kernel
      have hl : raw35800step1Labels = labelEmbedding1 ∘ raw35800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35800step1 raw35800step1Labels raw35800step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw35801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35801step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35801 raw35801Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw35801 raw35801Labels = mixedMoment B raw35801step0 raw35801step0Labels := by
      have ha : raw35801step0 = (fun i j => raw35801 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35801step0 raw35801; decide +kernel
      have hl : raw35801step0Labels = raw35801Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35801 raw35801Labels permutation161 permutation5
    mixedMoment B raw35801step0 raw35801step0Labels = mixedMoment B raw35801step1 raw35801step1Labels := by
      have ha : raw35801step1 = -raw35801step0 := by apply Matrix.ext; change ∀ i j, raw35801step1 i j = -(raw35801step0 i j); unfold raw35801step1 raw35801step0; decide +kernel
      have hl : raw35801step1Labels = raw35801step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35801step1 raw35801step1Labels = mixedMoment B raw35801step2 raw35801step2Labels := by
      have ha : raw35801step2 = raw35801step1 := by apply Matrix.ext; unfold raw35801step2 raw35801step1; decide +kernel
      have hl : raw35801step1Labels = labelEmbedding1 ∘ raw35801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35801step1 raw35801step1Labels raw35801step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

def raw35802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35802step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35802 raw35802Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw35802 raw35802Labels = mixedMoment B raw35802step0 raw35802step0Labels := by
      have ha : raw35802step0 = (fun i j => raw35802 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35802step0 raw35802; decide +kernel
      have hl : raw35802step0Labels = raw35802Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35802 raw35802Labels permutation289 permutation7
    mixedMoment B raw35802step0 raw35802step0Labels = mixedMoment B raw35802step1 raw35802step1Labels := by
      have ha : raw35802step1 = -raw35802step0 := by apply Matrix.ext; change ∀ i j, raw35802step1 i j = -(raw35802step0 i j); unfold raw35802step1 raw35802step0; decide +kernel
      have hl : raw35802step1Labels = raw35802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35802step1 raw35802step1Labels = mixedMoment B raw35802step2 raw35802step2Labels := by
      have ha : raw35802step2 = raw35802step1 := by apply Matrix.ext; unfold raw35802step2 raw35802step1; decide +kernel
      have hl : raw35802step1Labels = labelEmbedding1 ∘ raw35802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35802step1 raw35802step1Labels raw35802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

def raw35803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35803step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35803 raw35803Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw35803 raw35803Labels = mixedMoment B raw35803step0 raw35803step0Labels := by
      have ha : raw35803step0 = (fun i j => raw35803 (permutation203 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35803step0 raw35803; decide +kernel
      have hl : raw35803step0Labels = raw35803Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35803 raw35803Labels permutation203 permutation5
    mixedMoment B raw35803step0 raw35803step0Labels = mixedMoment B raw35803step1 raw35803step1Labels := by
      have ha : raw35803step1 = -raw35803step0 := by apply Matrix.ext; change ∀ i j, raw35803step1 i j = -(raw35803step0 i j); unfold raw35803step1 raw35803step0; decide +kernel
      have hl : raw35803step1Labels = raw35803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35803step1 raw35803step1Labels = mixedMoment B raw35803step2 raw35803step2Labels := by
      have ha : raw35803step2 = raw35803step1 := by apply Matrix.ext; unfold raw35803step2 raw35803step1; decide +kernel
      have hl : raw35803step1Labels = labelEmbedding1 ∘ raw35803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35803step1 raw35803step1Labels raw35803step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw35804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35804step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35804step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35804 raw35804Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw35804 raw35804Labels = mixedMoment B raw35804step0 raw35804step0Labels := by
      have ha : raw35804step0 = (fun i j => raw35804 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35804step0 raw35804; decide +kernel
      have hl : raw35804step0Labels = raw35804Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35804 raw35804Labels permutation227 permutation5
    mixedMoment B raw35804step0 raw35804step0Labels = mixedMoment B raw35804step1 raw35804step1Labels := by
      have ha : raw35804step1 = -raw35804step0 := by apply Matrix.ext; change ∀ i j, raw35804step1 i j = -(raw35804step0 i j); unfold raw35804step1 raw35804step0; decide +kernel
      have hl : raw35804step1Labels = raw35804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35804step1 raw35804step1Labels = mixedMoment B raw35804step2 raw35804step2Labels := by
      have ha : raw35804step2 = raw35804step1 := by apply Matrix.ext; unfold raw35804step2 raw35804step1; decide +kernel
      have hl : raw35804step1Labels = labelEmbedding1 ∘ raw35804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35804step1 raw35804step1Labels raw35804step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw35805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35805step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35805step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35805 raw35805Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw35805 raw35805Labels = mixedMoment B raw35805step0 raw35805step0Labels := by
      have ha : raw35805step0 = (fun i j => raw35805 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35805step0 raw35805; decide +kernel
      have hl : raw35805step0Labels = raw35805Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35805 raw35805Labels permutation289 permutation7
    mixedMoment B raw35805step0 raw35805step0Labels = mixedMoment B raw35805step1 raw35805step1Labels := by
      have ha : raw35805step1 = -raw35805step0 := by apply Matrix.ext; change ∀ i j, raw35805step1 i j = -(raw35805step0 i j); unfold raw35805step1 raw35805step0; decide +kernel
      have hl : raw35805step1Labels = raw35805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35805step1 raw35805step1Labels = mixedMoment B raw35805step2 raw35805step2Labels := by
      have ha : raw35805step2 = raw35805step1 := by apply Matrix.ext; unfold raw35805step2 raw35805step1; decide +kernel
      have hl : raw35805step1Labels = labelEmbedding1 ∘ raw35805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35805step1 raw35805step1Labels raw35805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3867 node3867Labels := by rfl

def raw35806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35806step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35806 raw35806Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw35806 raw35806Labels = mixedMoment B raw35806step0 raw35806step0Labels := by
      have ha : raw35806step0 = (fun i j => raw35806 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35806step0 raw35806; decide +kernel
      have hl : raw35806step0Labels = raw35806Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35806 raw35806Labels permutation164 permutation5
    mixedMoment B raw35806step0 raw35806step0Labels = mixedMoment B raw35806step1 raw35806step1Labels := by
      have ha : raw35806step1 = -raw35806step0 := by apply Matrix.ext; change ∀ i j, raw35806step1 i j = -(raw35806step0 i j); unfold raw35806step1 raw35806step0; decide +kernel
      have hl : raw35806step1Labels = raw35806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35806step1 raw35806step1Labels = mixedMoment B raw35806step2 raw35806step2Labels := by
      have ha : raw35806step2 = raw35806step1 := by apply Matrix.ext; unfold raw35806step2 raw35806step1; decide +kernel
      have hl : raw35806step1Labels = labelEmbedding1 ∘ raw35806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35806step1 raw35806step1Labels raw35806step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

def raw35807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35807 raw35807Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw35807 raw35807Labels = mixedMoment B raw35807step0 raw35807step0Labels := by
      have ha : raw35807step0 = (fun i j => raw35807 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35807step0 raw35807; decide +kernel
      have hl : raw35807step0Labels = raw35807Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35807 raw35807Labels permutation291 permutation7
    mixedMoment B raw35807step0 raw35807step0Labels = mixedMoment B raw35807step1 raw35807step1Labels := by
      have ha : raw35807step1 = -raw35807step0 := by apply Matrix.ext; change ∀ i j, raw35807step1 i j = -(raw35807step0 i j); unfold raw35807step1 raw35807step0; decide +kernel
      have hl : raw35807step1Labels = raw35807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35807step1 raw35807step1Labels = mixedMoment B raw35807step2 raw35807step2Labels := by
      have ha : raw35807step2 = raw35807step1 := by apply Matrix.ext; unfold raw35807step2 raw35807step1; decide +kernel
      have hl : raw35807step1Labels = labelEmbedding1 ∘ raw35807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35807step1 raw35807step1Labels raw35807step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

def raw35808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35808step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35808 raw35808Labels = mixedMoment B node3792 node3792Labels := by
  calc
    mixedMoment B raw35808 raw35808Labels = mixedMoment B raw35808step0 raw35808step0Labels := by
      have ha : raw35808step0 = (fun i j => raw35808 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35808step0 raw35808; decide +kernel
      have hl : raw35808step0Labels = raw35808Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35808 raw35808Labels permutation291 permutation7
    mixedMoment B raw35808step0 raw35808step0Labels = mixedMoment B raw35808step1 raw35808step1Labels := by
      have ha : raw35808step1 = -raw35808step0 := by apply Matrix.ext; change ∀ i j, raw35808step1 i j = -(raw35808step0 i j); unfold raw35808step1 raw35808step0; decide +kernel
      have hl : raw35808step1Labels = raw35808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35808step1 raw35808step1Labels = mixedMoment B raw35808step2 raw35808step2Labels := by
      have ha : raw35808step2 = raw35808step1 := by apply Matrix.ext; unfold raw35808step2 raw35808step1; decide +kernel
      have hl : raw35808step1Labels = labelEmbedding1 ∘ raw35808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35808step1 raw35808step1Labels raw35808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3792 node3792Labels := by rfl

def raw35809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35809step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35809step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35809 raw35809Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw35809 raw35809Labels = mixedMoment B raw35809step0 raw35809step0Labels := by
      have ha : raw35809step0 = (fun i j => raw35809 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35809step0 raw35809; decide +kernel
      have hl : raw35809step0Labels = raw35809Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35809 raw35809Labels permutation224 permutation5
    mixedMoment B raw35809step0 raw35809step0Labels = mixedMoment B raw35809step1 raw35809step1Labels := by
      have ha : raw35809step1 = -raw35809step0 := by apply Matrix.ext; change ∀ i j, raw35809step1 i j = -(raw35809step0 i j); unfold raw35809step1 raw35809step0; decide +kernel
      have hl : raw35809step1Labels = raw35809step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35809step1 raw35809step1Labels = mixedMoment B raw35809step2 raw35809step2Labels := by
      have ha : raw35809step2 = raw35809step1 := by apply Matrix.ext; unfold raw35809step2 raw35809step1; decide +kernel
      have hl : raw35809step1Labels = labelEmbedding1 ∘ raw35809step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35809step1 raw35809step1Labels raw35809step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

def raw35810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35810step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35810step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35810step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35810 raw35810Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw35810 raw35810Labels = mixedMoment B raw35810step0 raw35810step0Labels := by
      have ha : raw35810step0 = (fun i j => raw35810 (permutation292 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35810step0 raw35810; decide +kernel
      have hl : raw35810step0Labels = raw35810Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35810 raw35810Labels permutation292 permutation7
    mixedMoment B raw35810step0 raw35810step0Labels = mixedMoment B raw35810step1 raw35810step1Labels := by
      have ha : raw35810step1 = -raw35810step0 := by apply Matrix.ext; change ∀ i j, raw35810step1 i j = -(raw35810step0 i j); unfold raw35810step1 raw35810step0; decide +kernel
      have hl : raw35810step1Labels = raw35810step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35810step1 raw35810step1Labels = mixedMoment B raw35810step2 raw35810step2Labels := by
      have ha : raw35810step2 = raw35810step1 := by apply Matrix.ext; unfold raw35810step2 raw35810step1; decide +kernel
      have hl : raw35810step1Labels = labelEmbedding1 ∘ raw35810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35810step1 raw35810step1Labels raw35810step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

def raw35811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35811step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35811step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35811 raw35811Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw35811 raw35811Labels = mixedMoment B raw35811step0 raw35811step0Labels := by
      have ha : raw35811step0 = (fun i j => raw35811 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35811step0 raw35811; decide +kernel
      have hl : raw35811step0Labels = raw35811Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35811 raw35811Labels permutation158 permutation5
    mixedMoment B raw35811step0 raw35811step0Labels = mixedMoment B raw35811step1 raw35811step1Labels := by
      have ha : raw35811step1 = -raw35811step0 := by apply Matrix.ext; change ∀ i j, raw35811step1 i j = -(raw35811step0 i j); unfold raw35811step1 raw35811step0; decide +kernel
      have hl : raw35811step1Labels = raw35811step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35811step1 raw35811step1Labels = mixedMoment B raw35811step2 raw35811step2Labels := by
      have ha : raw35811step2 = raw35811step1 := by apply Matrix.ext; unfold raw35811step2 raw35811step1; decide +kernel
      have hl : raw35811step1Labels = labelEmbedding1 ∘ raw35811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35811step1 raw35811step1Labels raw35811step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

def raw35812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35812 raw35812Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw35812 raw35812Labels = mixedMoment B raw35812step0 raw35812step0Labels := by
      have ha : raw35812step0 = (fun i j => raw35812 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35812step0 raw35812; decide +kernel
      have hl : raw35812step0Labels = raw35812Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35812 raw35812Labels permutation289 permutation7
    mixedMoment B raw35812step0 raw35812step0Labels = mixedMoment B raw35812step1 raw35812step1Labels := by
      have ha : raw35812step1 = -raw35812step0 := by apply Matrix.ext; change ∀ i j, raw35812step1 i j = -(raw35812step0 i j); unfold raw35812step1 raw35812step0; decide +kernel
      have hl : raw35812step1Labels = raw35812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35812step1 raw35812step1Labels = mixedMoment B raw35812step2 raw35812step2Labels := by
      have ha : raw35812step2 = raw35812step1 := by apply Matrix.ext; unfold raw35812step2 raw35812step1; decide +kernel
      have hl : raw35812step1Labels = labelEmbedding1 ∘ raw35812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35812step1 raw35812step1Labels raw35812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

def raw35813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35813step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35813step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35813step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35813 raw35813Labels = mixedMoment B node3792 node3792Labels := by
  calc
    mixedMoment B raw35813 raw35813Labels = mixedMoment B raw35813step0 raw35813step0Labels := by
      have ha : raw35813step0 = (fun i j => raw35813 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35813step0 raw35813; decide +kernel
      have hl : raw35813step0Labels = raw35813Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35813 raw35813Labels permutation289 permutation7
    mixedMoment B raw35813step0 raw35813step0Labels = mixedMoment B raw35813step1 raw35813step1Labels := by
      have ha : raw35813step1 = -raw35813step0 := by apply Matrix.ext; change ∀ i j, raw35813step1 i j = -(raw35813step0 i j); unfold raw35813step1 raw35813step0; decide +kernel
      have hl : raw35813step1Labels = raw35813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35813step1 raw35813step1Labels = mixedMoment B raw35813step2 raw35813step2Labels := by
      have ha : raw35813step2 = raw35813step1 := by apply Matrix.ext; unfold raw35813step2 raw35813step1; decide +kernel
      have hl : raw35813step1Labels = labelEmbedding1 ∘ raw35813step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35813step1 raw35813step1Labels raw35813step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3792 node3792Labels := by rfl

def raw35814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35814step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35814 raw35814Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw35814 raw35814Labels = mixedMoment B raw35814step0 raw35814step0Labels := by
      have ha : raw35814step0 = (fun i j => raw35814 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35814step0 raw35814; decide +kernel
      have hl : raw35814step0Labels = raw35814Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35814 raw35814Labels permutation200 permutation5
    mixedMoment B raw35814step0 raw35814step0Labels = mixedMoment B raw35814step1 raw35814step1Labels := by
      have ha : raw35814step1 = -raw35814step0 := by apply Matrix.ext; change ∀ i j, raw35814step1 i j = -(raw35814step0 i j); unfold raw35814step1 raw35814step0; decide +kernel
      have hl : raw35814step1Labels = raw35814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35814step1 raw35814step1Labels = mixedMoment B raw35814step2 raw35814step2Labels := by
      have ha : raw35814step2 = raw35814step1 := by apply Matrix.ext; unfold raw35814step2 raw35814step1; decide +kernel
      have hl : raw35814step1Labels = labelEmbedding1 ∘ raw35814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35814step1 raw35814step1Labels raw35814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

def raw35815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw35815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35815step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35815step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35815 raw35815Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw35815 raw35815Labels = mixedMoment B raw35815step0 raw35815step0Labels := by
      have ha : raw35815step0 = (fun i j => raw35815 (permutation290 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35815step0 raw35815; decide +kernel
      have hl : raw35815step0Labels = raw35815Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35815 raw35815Labels permutation290 permutation7
    mixedMoment B raw35815step0 raw35815step0Labels = mixedMoment B raw35815step1 raw35815step1Labels := by
      have ha : raw35815step1 = -raw35815step0 := by apply Matrix.ext; change ∀ i j, raw35815step1 i j = -(raw35815step0 i j); unfold raw35815step1 raw35815step0; decide +kernel
      have hl : raw35815step1Labels = raw35815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35815step1 raw35815step1Labels = mixedMoment B raw35815step2 raw35815step2Labels := by
      have ha : raw35815step2 = raw35815step1 := by apply Matrix.ext; unfold raw35815step2 raw35815step1; decide +kernel
      have hl : raw35815step1Labels = labelEmbedding1 ∘ raw35815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35815step1 raw35815step1Labels raw35815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

def raw35816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw35816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw35816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35816step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw35816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35816 raw35816Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw35816 raw35816Labels = mixedMoment B raw35816step0 raw35816step0Labels := by
      have ha : raw35816step0 = (fun i j => raw35816 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35816step0 raw35816; decide +kernel
      have hl : raw35816step0Labels = raw35816Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35816 raw35816Labels permutation160 permutation5
    mixedMoment B raw35816step0 raw35816step0Labels = mixedMoment B raw35816step1 raw35816step1Labels := by
      have ha : raw35816step1 = -raw35816step0 := by apply Matrix.ext; change ∀ i j, raw35816step1 i j = -(raw35816step0 i j); unfold raw35816step1 raw35816step0; decide +kernel
      have hl : raw35816step1Labels = raw35816step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35816step1 raw35816step1Labels = mixedMoment B raw35816step2 raw35816step2Labels := by
      have ha : raw35816step2 = raw35816step1 := by apply Matrix.ext; unfold raw35816step2 raw35816step1; decide +kernel
      have hl : raw35816step1Labels = labelEmbedding1 ∘ raw35816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35816step1 raw35816step1Labels raw35816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2140 node2140Labels := by rfl

def raw35817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw35817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw35817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35817step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw35817step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35817 raw35817Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw35817 raw35817Labels = mixedMoment B raw35817step0 raw35817step0Labels := by
      have ha : raw35817step0 = (fun i j => raw35817 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35817step0 raw35817; decide +kernel
      have hl : raw35817step0Labels = raw35817Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35817 raw35817Labels permutation289 permutation7
    mixedMoment B raw35817step0 raw35817step0Labels = mixedMoment B raw35817step1 raw35817step1Labels := by
      have ha : raw35817step1 = -raw35817step0 := by apply Matrix.ext; change ∀ i j, raw35817step1 i j = -(raw35817step0 i j); unfold raw35817step1 raw35817step0; decide +kernel
      have hl : raw35817step1Labels = raw35817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35817step1 raw35817step1Labels = mixedMoment B raw35817step2 raw35817step2Labels := by
      have ha : raw35817step2 = raw35817step1 := by apply Matrix.ext; unfold raw35817step2 raw35817step1; decide +kernel
      have hl : raw35817step1Labels = labelEmbedding1 ∘ raw35817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35817step1 raw35817step1Labels raw35817step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

def raw35818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw35818step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw35818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35818 raw35818Labels = mixedMoment B node3597 node3597Labels := by
  calc
    mixedMoment B raw35818 raw35818Labels = mixedMoment B raw35818step0 raw35818step0Labels := by
      have ha : raw35818step0 = (fun i j => raw35818 (permutation664 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35818step0 raw35818; decide +kernel
      have hl : raw35818step0Labels = raw35818Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35818 raw35818Labels permutation664 permutation5
    mixedMoment B raw35818step0 raw35818step0Labels = mixedMoment B raw35818step1 raw35818step1Labels := by
      have ha : raw35818step1 = raw35818step0 := by apply Matrix.ext; unfold raw35818step1 raw35818step0; decide +kernel
      have hl : raw35818step0Labels = labelEmbedding1 ∘ raw35818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35818step0 raw35818step0Labels raw35818step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3597 node3597Labels := by rfl

def raw35819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35819step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35819 raw35819Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw35819 raw35819Labels = mixedMoment B raw35819step0 raw35819step0Labels := by
      have ha : raw35819step0 = (fun i j => raw35819 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35819step0 raw35819; decide +kernel
      have hl : raw35819step0Labels = raw35819Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35819 raw35819Labels permutation644 permutation5
    mixedMoment B raw35819step0 raw35819step0Labels = mixedMoment B raw35819step1 raw35819step1Labels := by
      have ha : raw35819step1 = raw35819step0 := by apply Matrix.ext; unfold raw35819step1 raw35819step0; decide +kernel
      have hl : raw35819step0Labels = labelEmbedding1 ∘ raw35819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35819step0 raw35819step0Labels raw35819step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw35820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw35820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35820 raw35820Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw35820 raw35820Labels = mixedMoment B raw35820step0 raw35820step0Labels := by
      have ha : raw35820step0 = (fun i j => raw35820 (permutation638 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35820step0 raw35820; decide +kernel
      have hl : raw35820step0Labels = raw35820Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35820 raw35820Labels permutation638 permutation5
    mixedMoment B raw35820step0 raw35820step0Labels = mixedMoment B raw35820step1 raw35820step1Labels := by
      have ha : raw35820step1 = raw35820step0 := by apply Matrix.ext; unfold raw35820step1 raw35820step0; decide +kernel
      have hl : raw35820step0Labels = labelEmbedding1 ∘ raw35820step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35820step0 raw35820step0Labels raw35820step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw35821 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35821step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35821step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35821 raw35821Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw35821 raw35821Labels = mixedMoment B raw35821step0 raw35821step0Labels := by
      have ha : raw35821step0 = (fun i j => raw35821 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35821step0 raw35821; decide +kernel
      have hl : raw35821step0Labels = raw35821Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35821 raw35821Labels permutation152 permutation7
    mixedMoment B raw35821step0 raw35821step0Labels = mixedMoment B raw35821step1 raw35821step1Labels := by
      have ha : raw35821step1 = raw35821step0 := by apply Matrix.ext; unfold raw35821step1 raw35821step0; decide +kernel
      have hl : raw35821step0Labels = labelEmbedding10 ∘ raw35821step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35821step0 raw35821step0Labels raw35821step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

def raw35822 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35822step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35822 raw35822Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw35822 raw35822Labels = mixedMoment B raw35822step0 raw35822step0Labels := by
      have ha : raw35822step0 = (fun i j => raw35822 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35822step0 raw35822; decide +kernel
      have hl : raw35822step0Labels = raw35822Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35822 raw35822Labels permutation267 permutation7
    mixedMoment B raw35822step0 raw35822step0Labels = mixedMoment B raw35822step1 raw35822step1Labels := by
      have ha : raw35822step1 = raw35822step0 := by apply Matrix.ext; unfold raw35822step1 raw35822step0; decide +kernel
      have hl : raw35822step0Labels = labelEmbedding10 ∘ raw35822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35822step0 raw35822step0Labels raw35822step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw35823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw35823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35823step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35823 raw35823Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw35823 raw35823Labels = mixedMoment B raw35823step0 raw35823step0Labels := by
      have ha : raw35823step0 = (fun i j => raw35823 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35823step0 raw35823; decide +kernel
      have hl : raw35823step0Labels = raw35823Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35823 raw35823Labels permutation265 permutation7
    mixedMoment B raw35823step0 raw35823step0Labels = mixedMoment B raw35823step1 raw35823step1Labels := by
      have ha : raw35823step1 = raw35823step0 := by apply Matrix.ext; unfold raw35823step1 raw35823step0; decide +kernel
      have hl : raw35823step0Labels = labelEmbedding10 ∘ raw35823step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35823step0 raw35823step0Labels raw35823step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw35824 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35824step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35824 raw35824Labels = mixedMoment B node5345 node5345Labels := by
  calc
    mixedMoment B raw35824 raw35824Labels = mixedMoment B raw35824step0 raw35824step0Labels := by
      have ha : raw35824step0 = (fun i j => raw35824 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35824step0 raw35824; decide +kernel
      have hl : raw35824step0Labels = raw35824Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35824 raw35824Labels permutation265 permutation7
    mixedMoment B raw35824step0 raw35824step0Labels = mixedMoment B raw35824step1 raw35824step1Labels := by
      have ha : raw35824step1 = raw35824step0 := by apply Matrix.ext; unfold raw35824step1 raw35824step0; decide +kernel
      have hl : raw35824step0Labels = labelEmbedding10 ∘ raw35824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35824step0 raw35824step0Labels raw35824step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5345 node5345Labels := by rfl

def raw35825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35825 raw35825Labels = mixedMoment B node5157 node5157Labels := by
  calc
    mixedMoment B raw35825 raw35825Labels = mixedMoment B raw35825step0 raw35825step0Labels := by
      have ha : raw35825step0 = (fun i j => raw35825 (permutation289 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35825step0 raw35825; decide +kernel
      have hl : raw35825step0Labels = raw35825Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35825 raw35825Labels permutation289 permutation2
    mixedMoment B raw35825step0 raw35825step0Labels = mixedMoment B raw35825step1 raw35825step1Labels := by
      have ha : raw35825step1 = -raw35825step0 := by apply Matrix.ext; change ∀ i j, raw35825step1 i j = -(raw35825step0 i j); unfold raw35825step1 raw35825step0; decide +kernel
      have hl : raw35825step1Labels = raw35825step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5157 node5157Labels := by rfl

def raw35826 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35826 raw35826Labels = mixedMoment B node5124 node5124Labels := by
  calc
    mixedMoment B raw35826 raw35826Labels = mixedMoment B raw35826step0 raw35826step0Labels := by
      have ha : raw35826step0 = (fun i j => raw35826 (permutation292 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35826step0 raw35826; decide +kernel
      have hl : raw35826step0Labels = raw35826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35826 raw35826Labels permutation292 permutation2
    mixedMoment B raw35826step0 raw35826step0Labels = mixedMoment B raw35826step1 raw35826step1Labels := by
      have ha : raw35826step1 = -raw35826step0 := by apply Matrix.ext; change ∀ i j, raw35826step1 i j = -(raw35826step0 i j); unfold raw35826step1 raw35826step0; decide +kernel
      have hl : raw35826step1Labels = raw35826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5124 node5124Labels := by rfl

def raw35827 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw35827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35827 raw35827Labels = mixedMoment B node5124 node5124Labels := by
  calc
    mixedMoment B raw35827 raw35827Labels = mixedMoment B raw35827step0 raw35827step0Labels := by
      have ha : raw35827step0 = (fun i j => raw35827 (permutation290 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35827step0 raw35827; decide +kernel
      have hl : raw35827step0Labels = raw35827Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35827 raw35827Labels permutation290 permutation2
    mixedMoment B raw35827step0 raw35827step0Labels = mixedMoment B raw35827step1 raw35827step1Labels := by
      have ha : raw35827step1 = -raw35827step0 := by apply Matrix.ext; change ∀ i j, raw35827step1 i j = -(raw35827step0 i j); unfold raw35827step1 raw35827step0; decide +kernel
      have hl : raw35827step1Labels = raw35827step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5124 node5124Labels := by rfl

def raw35828 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35828 raw35828Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw35828 raw35828Labels = mixedMoment B raw35828step0 raw35828step0Labels := by
      have ha : raw35828step0 = (fun i j => raw35828 (permutation289 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35828step0 raw35828; decide +kernel
      have hl : raw35828step0Labels = raw35828Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35828 raw35828Labels permutation289 permutation2
    mixedMoment B raw35828step0 raw35828step0Labels = mixedMoment B raw35828step1 raw35828step1Labels := by
      have ha : raw35828step1 = -raw35828step0 := by apply Matrix.ext; change ∀ i j, raw35828step1 i j = -(raw35828step0 i j); unfold raw35828step1 raw35828step0; decide +kernel
      have hl : raw35828step1Labels = raw35828step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw35829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw35829step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35829step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35829step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35829step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35829 raw35829Labels = mixedMoment B node5221 node5221Labels := by
  calc
    mixedMoment B raw35829 raw35829Labels = mixedMoment B raw35829step0 raw35829step0Labels := by
      have ha : raw35829step0 = (fun i j => raw35829 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35829step0 raw35829; decide +kernel
      have hl : raw35829step0Labels = raw35829Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35829 raw35829Labels permutation161 permutation4
    mixedMoment B raw35829step0 raw35829step0Labels = mixedMoment B raw35829step1 raw35829step1Labels := by
      have ha : raw35829step1 = -raw35829step0 := by apply Matrix.ext; change ∀ i j, raw35829step1 i j = -(raw35829step0 i j); unfold raw35829step1 raw35829step0; decide +kernel
      have hl : raw35829step1Labels = raw35829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35829step1 raw35829step1Labels = mixedMoment B raw35829step2 raw35829step2Labels := by
      have ha : raw35829step2 = raw35829step1 := by apply Matrix.ext; unfold raw35829step2 raw35829step1; decide +kernel
      have hl : raw35829step1Labels = labelEmbedding7 ∘ raw35829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35829step1 raw35829step1Labels raw35829step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5221 node5221Labels := by rfl

def raw35830 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35830step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35830 raw35830Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw35830 raw35830Labels = mixedMoment B raw35830step0 raw35830step0Labels := by
      have ha : raw35830step0 = (fun i j => raw35830 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35830step0 raw35830; decide +kernel
      have hl : raw35830step0Labels = raw35830Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35830 raw35830Labels permutation152 permutation6
    mixedMoment B raw35830step0 raw35830step0Labels = mixedMoment B raw35830step1 raw35830step1Labels := by
      have ha : raw35830step1 = raw35830step0 := by apply Matrix.ext; unfold raw35830step1 raw35830step0; decide +kernel
      have hl : raw35830step0Labels = labelEmbedding9 ∘ raw35830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35830step0 raw35830step0Labels raw35830step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw35831 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35831step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35831 raw35831Labels = mixedMoment B node5375 node5375Labels := by
  calc
    mixedMoment B raw35831 raw35831Labels = mixedMoment B raw35831step0 raw35831step0Labels := by
      have ha : raw35831step0 = (fun i j => raw35831 (permutation292 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35831step0 raw35831; decide +kernel
      have hl : raw35831step0Labels = raw35831Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35831 raw35831Labels permutation292 permutation2
    mixedMoment B raw35831step0 raw35831step0Labels = mixedMoment B raw35831step1 raw35831step1Labels := by
      have ha : raw35831step1 = -raw35831step0 := by apply Matrix.ext; change ∀ i j, raw35831step1 i j = -(raw35831step0 i j); unfold raw35831step1 raw35831step0; decide +kernel
      have hl : raw35831step1Labels = raw35831step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5375 node5375Labels := by rfl

def raw35832 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw35832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35832 raw35832Labels = mixedMoment B node5375 node5375Labels := by
  calc
    mixedMoment B raw35832 raw35832Labels = mixedMoment B raw35832step0 raw35832step0Labels := by
      have ha : raw35832step0 = (fun i j => raw35832 (permutation290 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35832step0 raw35832; decide +kernel
      have hl : raw35832step0Labels = raw35832Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35832 raw35832Labels permutation290 permutation2
    mixedMoment B raw35832step0 raw35832step0Labels = mixedMoment B raw35832step1 raw35832step1Labels := by
      have ha : raw35832step1 = -raw35832step0 := by apply Matrix.ext; change ∀ i j, raw35832step1 i j = -(raw35832step0 i j); unfold raw35832step1 raw35832step0; decide +kernel
      have hl : raw35832step1Labels = raw35832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5375 node5375Labels := by rfl

def raw35833 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35833 raw35833Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw35833 raw35833Labels = mixedMoment B raw35833step0 raw35833step0Labels := by
      have ha : raw35833step0 = (fun i j => raw35833 (permutation289 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35833step0 raw35833; decide +kernel
      have hl : raw35833step0Labels = raw35833Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35833 raw35833Labels permutation289 permutation2
    mixedMoment B raw35833step0 raw35833step0Labels = mixedMoment B raw35833step1 raw35833step1Labels := by
      have ha : raw35833step1 = -raw35833step0 := by apply Matrix.ext; change ∀ i j, raw35833step1 i j = -(raw35833step0 i j); unfold raw35833step1 raw35833step0; decide +kernel
      have hl : raw35833step1Labels = raw35833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5374 node5374Labels := by rfl

def raw35834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35834step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35834step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35834step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35834 raw35834Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw35834 raw35834Labels = mixedMoment B raw35834step0 raw35834step0Labels := by
      have ha : raw35834step0 = (fun i j => raw35834 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35834step0 raw35834; decide +kernel
      have hl : raw35834step0Labels = raw35834Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35834 raw35834Labels permutation164 permutation4
    mixedMoment B raw35834step0 raw35834step0Labels = mixedMoment B raw35834step1 raw35834step1Labels := by
      have ha : raw35834step1 = -raw35834step0 := by apply Matrix.ext; change ∀ i j, raw35834step1 i j = -(raw35834step0 i j); unfold raw35834step1 raw35834step0; decide +kernel
      have hl : raw35834step1Labels = raw35834step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35834step1 raw35834step1Labels = mixedMoment B raw35834step2 raw35834step2Labels := by
      have ha : raw35834step2 = raw35834step1 := by apply Matrix.ext; unfold raw35834step2 raw35834step1; decide +kernel
      have hl : raw35834step1Labels = labelEmbedding7 ∘ raw35834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35834step1 raw35834step1Labels raw35834step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw35835 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35835step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35835 raw35835Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw35835 raw35835Labels = mixedMoment B raw35835step0 raw35835step0Labels := by
      have ha : raw35835step0 = (fun i j => raw35835 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35835step0 raw35835; decide +kernel
      have hl : raw35835step0Labels = raw35835Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35835 raw35835Labels permutation154 permutation6
    mixedMoment B raw35835step0 raw35835step0Labels = mixedMoment B raw35835step1 raw35835step1Labels := by
      have ha : raw35835step1 = raw35835step0 := by apply Matrix.ext; unfold raw35835step1 raw35835step0; decide +kernel
      have hl : raw35835step0Labels = labelEmbedding9 ∘ raw35835step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35835step0 raw35835step0Labels raw35835step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw35836 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw35836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35836step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35836 raw35836Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw35836 raw35836Labels = mixedMoment B raw35836step0 raw35836step0Labels := by
      have ha : raw35836step0 = (fun i j => raw35836 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35836step0 raw35836; decide +kernel
      have hl : raw35836step0Labels = raw35836Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35836 raw35836Labels permutation265 permutation7
    mixedMoment B raw35836step0 raw35836step0Labels = mixedMoment B raw35836step1 raw35836step1Labels := by
      have ha : raw35836step1 = raw35836step0 := by apply Matrix.ext; unfold raw35836step1 raw35836step0; decide +kernel
      have hl : raw35836step0Labels = labelEmbedding10 ∘ raw35836step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35836step0 raw35836step0Labels raw35836step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw35837 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35837step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35837 raw35837Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw35837 raw35837Labels = mixedMoment B raw35837step0 raw35837step0Labels := by
      have ha : raw35837step0 = (fun i j => raw35837 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35837step0 raw35837; decide +kernel
      have hl : raw35837step0Labels = raw35837Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35837 raw35837Labels permutation265 permutation7
    mixedMoment B raw35837step0 raw35837step0Labels = mixedMoment B raw35837step1 raw35837step1Labels := by
      have ha : raw35837step1 = raw35837step0 := by apply Matrix.ext; unfold raw35837step1 raw35837step0; decide +kernel
      have hl : raw35837step0Labels = labelEmbedding10 ∘ raw35837step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35837step0 raw35837step0Labels raw35837step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw35838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35838step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35838step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35838step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35838step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35838 raw35838Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw35838 raw35838Labels = mixedMoment B raw35838step0 raw35838step0Labels := by
      have ha : raw35838step0 = (fun i j => raw35838 (permutation299 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35838step0 raw35838; decide +kernel
      have hl : raw35838step0Labels = raw35838Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35838 raw35838Labels permutation299 permutation5
    mixedMoment B raw35838step0 raw35838step0Labels = mixedMoment B raw35838step1 raw35838step1Labels := by
      have ha : raw35838step1 = -raw35838step0 := by apply Matrix.ext; change ∀ i j, raw35838step1 i j = -(raw35838step0 i j); unfold raw35838step1 raw35838step0; decide +kernel
      have hl : raw35838step1Labels = raw35838step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35838step1 raw35838step1Labels = mixedMoment B raw35838step2 raw35838step2Labels := by
      have ha : raw35838step2 = raw35838step1 := by apply Matrix.ext; unfold raw35838step2 raw35838step1; decide +kernel
      have hl : raw35838step1Labels = labelEmbedding8 ∘ raw35838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35838step1 raw35838step1Labels raw35838step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw35839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35839step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35839step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35839step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35839step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35839 raw35839Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw35839 raw35839Labels = mixedMoment B raw35839step0 raw35839step0Labels := by
      have ha : raw35839step0 = (fun i j => raw35839 (permutation299 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35839step0 raw35839; decide +kernel
      have hl : raw35839step0Labels = raw35839Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35839 raw35839Labels permutation299 permutation5
    mixedMoment B raw35839step0 raw35839step0Labels = mixedMoment B raw35839step1 raw35839step1Labels := by
      have ha : raw35839step1 = -raw35839step0 := by apply Matrix.ext; change ∀ i j, raw35839step1 i j = -(raw35839step0 i j); unfold raw35839step1 raw35839step0; decide +kernel
      have hl : raw35839step1Labels = raw35839step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35839step1 raw35839step1Labels = mixedMoment B raw35839step2 raw35839step2Labels := by
      have ha : raw35839step2 = raw35839step1 := by apply Matrix.ext; unfold raw35839step2 raw35839step1; decide +kernel
      have hl : raw35839step1Labels = labelEmbedding8 ∘ raw35839step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35839step1 raw35839step1Labels raw35839step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
