import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19712step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19712step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19712step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19712 raw19712Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw19712 raw19712Labels = mixedMoment B raw19712step0 raw19712step0Labels := by
      have hz : ∀ j, raw19712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19712step0 = (fun i j => raw19712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19712step0 raw19712; decide +kernel
      have hl : raw19712step0Labels = raw19712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19712 raw19712Labels permutation434 hz
    mixedMoment B raw19712step0 raw19712step0Labels = mixedMoment B raw19712step1 raw19712step1Labels := by
      have ha : raw19712step1 = (fun i j => raw19712step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19712step1 raw19712step0; decide +kernel
      have hl : raw19712step1Labels = raw19712step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19712step0 raw19712step0Labels permutation145 permutation3
    mixedMoment B raw19712step1 raw19712step1Labels = mixedMoment B raw19712step2 raw19712step2Labels := by
      have ha : raw19712step2 = -raw19712step1 := by apply Matrix.ext; change ∀ i j, raw19712step2 i j = -(raw19712step1 i j); unfold raw19712step2 raw19712step1; decide +kernel
      have hl : raw19712step2Labels = raw19712step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19712step2 raw19712step2Labels = mixedMoment B raw19712step3 raw19712step3Labels := by
      have ha : raw19712step3 = raw19712step2 := by apply Matrix.ext; unfold raw19712step3 raw19712step2; decide +kernel
      have hl : raw19712step2Labels = labelEmbedding6 ∘ raw19712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19712step2 raw19712step2Labels raw19712step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw19713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19713step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19713step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19713step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19713step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19713 raw19713Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw19713 raw19713Labels = mixedMoment B raw19713step0 raw19713step0Labels := by
      have hz : ∀ j, raw19713 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19713step0 = (fun i j => raw19713 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19713step0 raw19713; decide +kernel
      have hl : raw19713step0Labels = raw19713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19713 raw19713Labels permutation265 hz
    mixedMoment B raw19713step0 raw19713step0Labels = mixedMoment B raw19713step1 raw19713step1Labels := by
      have ha : raw19713step1 = (fun i j => raw19713step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19713step1 raw19713step0; decide +kernel
      have hl : raw19713step1Labels = raw19713step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19713step0 raw19713step0Labels permutation139 permutation3
    mixedMoment B raw19713step1 raw19713step1Labels = mixedMoment B raw19713step2 raw19713step2Labels := by
      have ha : raw19713step2 = -raw19713step1 := by apply Matrix.ext; change ∀ i j, raw19713step2 i j = -(raw19713step1 i j); unfold raw19713step2 raw19713step1; decide +kernel
      have hl : raw19713step2Labels = raw19713step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19713step2 raw19713step2Labels = mixedMoment B raw19713step3 raw19713step3Labels := by
      have ha : raw19713step3 = raw19713step2 := by apply Matrix.ext; unfold raw19713step3 raw19713step2; decide +kernel
      have hl : raw19713step2Labels = labelEmbedding6 ∘ raw19713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19713step2 raw19713step2Labels raw19713step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw19714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19714step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19714step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19714step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19714step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19714step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19714 raw19714Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw19714 raw19714Labels = mixedMoment B raw19714step0 raw19714step0Labels := by
      have hz : ∀ j, raw19714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19714step0 = (fun i j => raw19714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19714step0 raw19714; decide +kernel
      have hl : raw19714step0Labels = raw19714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19714 raw19714Labels permutation434 hz
    mixedMoment B raw19714step0 raw19714step0Labels = mixedMoment B raw19714step1 raw19714step1Labels := by
      have hz : ∀ j, raw19714step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19714step1 = (fun i j => raw19714step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19714step1 raw19714step0; decide +kernel
      have hl : raw19714step1Labels = raw19714step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19714step0 raw19714step0Labels permutation56 hz
    mixedMoment B raw19714step1 raw19714step1Labels = mixedMoment B raw19714step2 raw19714step2Labels := by
      have ha : raw19714step2 = (fun i j => raw19714step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19714step2 raw19714step1; decide +kernel
      have hl : raw19714step2Labels = raw19714step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19714step1 raw19714step1Labels permutation29 permutation3
    mixedMoment B raw19714step2 raw19714step2Labels = mixedMoment B raw19714step3 raw19714step3Labels := by
      have ha : raw19714step3 = -raw19714step2 := by apply Matrix.ext; change ∀ i j, raw19714step3 i j = -(raw19714step2 i j); unfold raw19714step3 raw19714step2; decide +kernel
      have hl : raw19714step3Labels = raw19714step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19714step3 raw19714step3Labels = mixedMoment B raw19714step4 raw19714step4Labels := by
      have ha : raw19714step4 = raw19714step3 := by apply Matrix.ext; unfold raw19714step4 raw19714step3; decide +kernel
      have hl : raw19714step3Labels = labelEmbedding6 ∘ raw19714step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19714step3 raw19714step3Labels raw19714step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

def raw19715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19715step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19715step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19715step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19715 raw19715Labels = mixedMoment B node4146 node4146Labels := by
  calc
    mixedMoment B raw19715 raw19715Labels = mixedMoment B raw19715step0 raw19715step0Labels := by
      have hz : ∀ j, raw19715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19715step0 = (fun i j => raw19715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19715step0 raw19715; decide +kernel
      have hl : raw19715step0Labels = raw19715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19715 raw19715Labels permutation346 hz
    mixedMoment B raw19715step0 raw19715step0Labels = mixedMoment B raw19715step1 raw19715step1Labels := by
      have hz : ∀ j, raw19715step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19715step1 = (fun i j => raw19715step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19715step1 raw19715step0; decide +kernel
      have hl : raw19715step1Labels = raw19715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19715step0 raw19715step0Labels permutation56 hz
    mixedMoment B raw19715step1 raw19715step1Labels = mixedMoment B raw19715step2 raw19715step2Labels := by
      have ha : raw19715step2 = (fun i j => raw19715step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19715step2 raw19715step1; decide +kernel
      have hl : raw19715step2Labels = raw19715step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19715step1 raw19715step1Labels permutation10 permutation3
    mixedMoment B raw19715step2 raw19715step2Labels = mixedMoment B raw19715step3 raw19715step3Labels := by
      have ha : raw19715step3 = raw19715step2 := by apply Matrix.ext; unfold raw19715step3 raw19715step2; decide +kernel
      have hl : raw19715step2Labels = labelEmbedding6 ∘ raw19715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19715step2 raw19715step2Labels raw19715step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4146 node4146Labels := by rfl

def raw19716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19716step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19716step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19716step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19716 raw19716Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw19716 raw19716Labels = mixedMoment B raw19716step0 raw19716step0Labels := by
      have hz : ∀ j, raw19716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19716step0 = (fun i j => raw19716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19716step0 raw19716; decide +kernel
      have hl : raw19716step0Labels = raw19716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19716 raw19716Labels permutation346 hz
    mixedMoment B raw19716step0 raw19716step0Labels = mixedMoment B raw19716step1 raw19716step1Labels := by
      have ha : raw19716step1 = (fun i j => raw19716step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19716step1 raw19716step0; decide +kernel
      have hl : raw19716step1Labels = raw19716step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19716step0 raw19716step0Labels permutation145 permutation3
    mixedMoment B raw19716step1 raw19716step1Labels = mixedMoment B raw19716step2 raw19716step2Labels := by
      have ha : raw19716step2 = -raw19716step1 := by apply Matrix.ext; change ∀ i j, raw19716step2 i j = -(raw19716step1 i j); unfold raw19716step2 raw19716step1; decide +kernel
      have hl : raw19716step2Labels = raw19716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19716step2 raw19716step2Labels = mixedMoment B raw19716step3 raw19716step3Labels := by
      have ha : raw19716step3 = raw19716step2 := by apply Matrix.ext; unfold raw19716step3 raw19716step2; decide +kernel
      have hl : raw19716step2Labels = labelEmbedding6 ∘ raw19716step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19716step2 raw19716step2Labels raw19716step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw19717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19717step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19717step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19717step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19717step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19717 raw19717Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw19717 raw19717Labels = mixedMoment B raw19717step0 raw19717step0Labels := by
      have hz : ∀ j, raw19717 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19717step0 = (fun i j => raw19717 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19717step0 raw19717; decide +kernel
      have hl : raw19717step0Labels = raw19717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19717 raw19717Labels permutation265 hz
    mixedMoment B raw19717step0 raw19717step0Labels = mixedMoment B raw19717step1 raw19717step1Labels := by
      have ha : raw19717step1 = (fun i j => raw19717step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19717step1 raw19717step0; decide +kernel
      have hl : raw19717step1Labels = raw19717step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19717step0 raw19717step0Labels permutation145 permutation3
    mixedMoment B raw19717step1 raw19717step1Labels = mixedMoment B raw19717step2 raw19717step2Labels := by
      have ha : raw19717step2 = -raw19717step1 := by apply Matrix.ext; change ∀ i j, raw19717step2 i j = -(raw19717step1 i j); unfold raw19717step2 raw19717step1; decide +kernel
      have hl : raw19717step2Labels = raw19717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19717step2 raw19717step2Labels = mixedMoment B raw19717step3 raw19717step3Labels := by
      have ha : raw19717step3 = raw19717step2 := by apply Matrix.ext; unfold raw19717step3 raw19717step2; decide +kernel
      have hl : raw19717step2Labels = labelEmbedding6 ∘ raw19717step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19717step2 raw19717step2Labels raw19717step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw19718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19718step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19718step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19718step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19718step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19718step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19718step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19718step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19718 raw19718Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw19718 raw19718Labels = mixedMoment B raw19718step0 raw19718step0Labels := by
      have hz : ∀ j, raw19718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19718step0 = (fun i j => raw19718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19718step0 raw19718; decide +kernel
      have hl : raw19718step0Labels = raw19718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19718 raw19718Labels permutation346 hz
    mixedMoment B raw19718step0 raw19718step0Labels = mixedMoment B raw19718step1 raw19718step1Labels := by
      have hz : ∀ j, raw19718step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19718step1 = (fun i j => raw19718step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19718step1 raw19718step0; decide +kernel
      have hl : raw19718step1Labels = raw19718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19718step0 raw19718step0Labels permutation56 hz
    mixedMoment B raw19718step1 raw19718step1Labels = mixedMoment B raw19718step2 raw19718step2Labels := by
      have ha : raw19718step2 = (fun i j => raw19718step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19718step2 raw19718step1; decide +kernel
      have hl : raw19718step2Labels = raw19718step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19718step1 raw19718step1Labels permutation29 permutation3
    mixedMoment B raw19718step2 raw19718step2Labels = mixedMoment B raw19718step3 raw19718step3Labels := by
      have ha : raw19718step3 = -raw19718step2 := by apply Matrix.ext; change ∀ i j, raw19718step3 i j = -(raw19718step2 i j); unfold raw19718step3 raw19718step2; decide +kernel
      have hl : raw19718step3Labels = raw19718step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19718step3 raw19718step3Labels = mixedMoment B raw19718step4 raw19718step4Labels := by
      have ha : raw19718step4 = raw19718step3 := by apply Matrix.ext; unfold raw19718step4 raw19718step3; decide +kernel
      have hl : raw19718step3Labels = labelEmbedding6 ∘ raw19718step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19718step3 raw19718step3Labels raw19718step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

def raw19719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19719step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![4, -3, -1]]
def raw19719step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19719step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19719step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19719step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19719step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19719 raw19719Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw19719 raw19719Labels = mixedMoment B raw19719step0 raw19719step0Labels := by
      have hz : ∀ j, raw19719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19719step0 = (fun i j => raw19719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19719step0 raw19719; decide +kernel
      have hl : raw19719step0Labels = raw19719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19719 raw19719Labels permutation434 hz
    mixedMoment B raw19719step0 raw19719step0Labels = mixedMoment B raw19719step1 raw19719step1Labels := by
      have hz : ∀ j, raw19719step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19719step1 = (fun i j => raw19719step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19719step1 raw19719step0; decide +kernel
      have hl : raw19719step1Labels = raw19719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19719step0 raw19719step0Labels permutation80 hz
    mixedMoment B raw19719step1 raw19719step1Labels = mixedMoment B raw19719step2 raw19719step2Labels := by
      have hz : ∀ j, raw19719step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19719step2 = (fun i j => raw19719step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19719step2 raw19719step1; decide +kernel
      have hl : raw19719step2Labels = raw19719step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19719step1 raw19719step1Labels permutation14 hz
    mixedMoment B raw19719step2 raw19719step2Labels = mixedMoment B raw19719step3 raw19719step3Labels := by
      have ha : raw19719step3 = (fun i j => raw19719step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19719step3 raw19719step2; decide +kernel
      have hl : raw19719step3Labels = raw19719step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19719step2 raw19719step2Labels permutation2 permutation3
    mixedMoment B raw19719step3 raw19719step3Labels = mixedMoment B raw19719step4 raw19719step4Labels := by
      have ha : raw19719step4 = raw19719step3 := by apply Matrix.ext; unfold raw19719step4 raw19719step3; decide +kernel
      have hl : raw19719step3Labels = labelEmbedding6 ∘ raw19719step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19719step3 raw19719step3Labels raw19719step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4181 node4181Labels := by rfl

def raw19720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19720step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19720step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19720step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19720step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19720 raw19720Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19720 raw19720Labels = mixedMoment B raw19720step0 raw19720step0Labels := by
      have hz : ∀ j, raw19720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19720step0 = (fun i j => raw19720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19720step0 raw19720; decide +kernel
      have hl : raw19720step0Labels = raw19720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19720 raw19720Labels permutation434 hz
    mixedMoment B raw19720step0 raw19720step0Labels = mixedMoment B raw19720step1 raw19720step1Labels := by
      have hz : ∀ j, raw19720step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19720step1 = (fun i j => raw19720step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19720step1 raw19720step0; decide +kernel
      have hl : raw19720step1Labels = raw19720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19720step0 raw19720step0Labels permutation80 hz
    mixedMoment B raw19720step1 raw19720step1Labels = mixedMoment B raw19720step2 raw19720step2Labels := by
      have ha : raw19720step2 = (fun i j => raw19720step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19720step2 raw19720step1; decide +kernel
      have hl : raw19720step2Labels = raw19720step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19720step1 raw19720step1Labels permutation31 permutation3
    mixedMoment B raw19720step2 raw19720step2Labels = mixedMoment B raw19720step3 raw19720step3Labels := by
      have ha : raw19720step3 = -raw19720step2 := by apply Matrix.ext; change ∀ i j, raw19720step3 i j = -(raw19720step2 i j); unfold raw19720step3 raw19720step2; decide +kernel
      have hl : raw19720step3Labels = raw19720step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19720step3 raw19720step3Labels = mixedMoment B raw19720step4 raw19720step4Labels := by
      have ha : raw19720step4 = raw19720step3 := by apply Matrix.ext; unfold raw19720step4 raw19720step3; decide +kernel
      have hl : raw19720step3Labels = labelEmbedding6 ∘ raw19720step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19720step3 raw19720step3Labels raw19720step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw19721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19721step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19721step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19721step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19721step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19721step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19721 raw19721Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19721 raw19721Labels = mixedMoment B raw19721step0 raw19721step0Labels := by
      have hz : ∀ j, raw19721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19721step0 = (fun i j => raw19721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19721step0 raw19721; decide +kernel
      have hl : raw19721step0Labels = raw19721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19721 raw19721Labels permutation434 hz
    mixedMoment B raw19721step0 raw19721step0Labels = mixedMoment B raw19721step1 raw19721step1Labels := by
      have hz : ∀ j, raw19721step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19721step1 = (fun i j => raw19721step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19721step1 raw19721step0; decide +kernel
      have hl : raw19721step1Labels = raw19721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19721step0 raw19721step0Labels permutation56 hz
    mixedMoment B raw19721step1 raw19721step1Labels = mixedMoment B raw19721step2 raw19721step2Labels := by
      have ha : raw19721step2 = (fun i j => raw19721step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19721step2 raw19721step1; decide +kernel
      have hl : raw19721step2Labels = raw19721step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19721step1 raw19721step1Labels permutation31 permutation3
    mixedMoment B raw19721step2 raw19721step2Labels = mixedMoment B raw19721step3 raw19721step3Labels := by
      have ha : raw19721step3 = -raw19721step2 := by apply Matrix.ext; change ∀ i j, raw19721step3 i j = -(raw19721step2 i j); unfold raw19721step3 raw19721step2; decide +kernel
      have hl : raw19721step3Labels = raw19721step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19721step3 raw19721step3Labels = mixedMoment B raw19721step4 raw19721step4Labels := by
      have ha : raw19721step4 = raw19721step3 := by apply Matrix.ext; unfold raw19721step4 raw19721step3; decide +kernel
      have hl : raw19721step3Labels = labelEmbedding6 ∘ raw19721step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19721step3 raw19721step3Labels raw19721step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw19722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19722step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19722step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19722step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19722step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19722step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19722 raw19722Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19722 raw19722Labels = mixedMoment B raw19722step0 raw19722step0Labels := by
      have hz : ∀ j, raw19722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19722step0 = (fun i j => raw19722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19722step0 raw19722; decide +kernel
      have hl : raw19722step0Labels = raw19722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19722 raw19722Labels permutation346 hz
    mixedMoment B raw19722step0 raw19722step0Labels = mixedMoment B raw19722step1 raw19722step1Labels := by
      have hz : ∀ j, raw19722step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19722step1 = (fun i j => raw19722step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19722step1 raw19722step0; decide +kernel
      have hl : raw19722step1Labels = raw19722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19722step0 raw19722step0Labels permutation56 hz
    mixedMoment B raw19722step1 raw19722step1Labels = mixedMoment B raw19722step2 raw19722step2Labels := by
      have ha : raw19722step2 = (fun i j => raw19722step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19722step2 raw19722step1; decide +kernel
      have hl : raw19722step2Labels = raw19722step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19722step1 raw19722step1Labels permutation31 permutation3
    mixedMoment B raw19722step2 raw19722step2Labels = mixedMoment B raw19722step3 raw19722step3Labels := by
      have ha : raw19722step3 = -raw19722step2 := by apply Matrix.ext; change ∀ i j, raw19722step3 i j = -(raw19722step2 i j); unfold raw19722step3 raw19722step2; decide +kernel
      have hl : raw19722step3Labels = raw19722step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19722step3 raw19722step3Labels = mixedMoment B raw19722step4 raw19722step4Labels := by
      have ha : raw19722step4 = raw19722step3 := by apply Matrix.ext; unfold raw19722step4 raw19722step3; decide +kernel
      have hl : raw19722step3Labels = labelEmbedding6 ∘ raw19722step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19722step3 raw19722step3Labels raw19722step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw19723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19723step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![5, -4, -1]]
def raw19723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19723step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-5, 2, 3]]
def raw19723step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19723step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw19723step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19723step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw19723step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19723 raw19723Labels = mixedMoment B node4112 node4112Labels := by
  calc
    mixedMoment B raw19723 raw19723Labels = mixedMoment B raw19723step0 raw19723step0Labels := by
      have hz : ∀ j, raw19723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19723step0 = (fun i j => raw19723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19723step0 raw19723; decide +kernel
      have hl : raw19723step0Labels = raw19723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19723 raw19723Labels permutation434 hz
    mixedMoment B raw19723step0 raw19723step0Labels = mixedMoment B raw19723step1 raw19723step1Labels := by
      have hz : ∀ j, raw19723step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19723step1 = (fun i j => raw19723step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19723step1 raw19723step0; decide +kernel
      have hl : raw19723step1Labels = raw19723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19723step0 raw19723step0Labels permutation80 hz
    mixedMoment B raw19723step1 raw19723step1Labels = mixedMoment B raw19723step2 raw19723step2Labels := by
      have hz : ∀ j, raw19723step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19723step2 = (fun i j => raw19723step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19723step2 raw19723step1; decide +kernel
      have hl : raw19723step2Labels = raw19723step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19723step1 raw19723step1Labels permutation14 hz
    mixedMoment B raw19723step2 raw19723step2Labels = mixedMoment B raw19723step3 raw19723step3Labels := by
      have ha : raw19723step3 = (fun i j => raw19723step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19723step3 raw19723step2; decide +kernel
      have hl : raw19723step3Labels = raw19723step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19723step2 raw19723step2Labels permutation7 permutation3
    mixedMoment B raw19723step3 raw19723step3Labels = mixedMoment B raw19723step4 raw19723step4Labels := by
      have ha : raw19723step4 = -raw19723step3 := by apply Matrix.ext; change ∀ i j, raw19723step4 i j = -(raw19723step3 i j); unfold raw19723step4 raw19723step3; decide +kernel
      have hl : raw19723step4Labels = raw19723step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19723step4 raw19723step4Labels = mixedMoment B raw19723step5 raw19723step5Labels := by
      have ha : raw19723step5 = raw19723step4 := by apply Matrix.ext; unfold raw19723step5 raw19723step4; decide +kernel
      have hl : raw19723step4Labels = labelEmbedding6 ∘ raw19723step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19723step4 raw19723step4Labels raw19723step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4112 node4112Labels := by rfl

def raw19724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19724step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19724step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19724step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19724step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19724step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19724 raw19724Labels = mixedMoment B node4108 node4108Labels := by
  calc
    mixedMoment B raw19724 raw19724Labels = mixedMoment B raw19724step0 raw19724step0Labels := by
      have hz : ∀ j, raw19724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19724step0 = (fun i j => raw19724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19724step0 raw19724; decide +kernel
      have hl : raw19724step0Labels = raw19724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19724 raw19724Labels permutation434 hz
    mixedMoment B raw19724step0 raw19724step0Labels = mixedMoment B raw19724step1 raw19724step1Labels := by
      have hz : ∀ j, raw19724step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19724step1 = (fun i j => raw19724step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19724step1 raw19724step0; decide +kernel
      have hl : raw19724step1Labels = raw19724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19724step0 raw19724step0Labels permutation80 hz
    mixedMoment B raw19724step1 raw19724step1Labels = mixedMoment B raw19724step2 raw19724step2Labels := by
      have ha : raw19724step2 = (fun i j => raw19724step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19724step2 raw19724step1; decide +kernel
      have hl : raw19724step2Labels = raw19724step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19724step1 raw19724step1Labels permutation31 permutation3
    mixedMoment B raw19724step2 raw19724step2Labels = mixedMoment B raw19724step3 raw19724step3Labels := by
      have ha : raw19724step3 = -raw19724step2 := by apply Matrix.ext; change ∀ i j, raw19724step3 i j = -(raw19724step2 i j); unfold raw19724step3 raw19724step2; decide +kernel
      have hl : raw19724step3Labels = raw19724step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19724step3 raw19724step3Labels = mixedMoment B raw19724step4 raw19724step4Labels := by
      have ha : raw19724step4 = raw19724step3 := by apply Matrix.ext; unfold raw19724step4 raw19724step3; decide +kernel
      have hl : raw19724step3Labels = labelEmbedding6 ∘ raw19724step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19724step3 raw19724step3Labels raw19724step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4108 node4108Labels := by rfl

def raw19725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19725step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19725step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19725step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19725step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19725step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19725 raw19725Labels = mixedMoment B node4108 node4108Labels := by
  calc
    mixedMoment B raw19725 raw19725Labels = mixedMoment B raw19725step0 raw19725step0Labels := by
      have hz : ∀ j, raw19725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19725step0 = (fun i j => raw19725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19725step0 raw19725; decide +kernel
      have hl : raw19725step0Labels = raw19725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19725 raw19725Labels permutation434 hz
    mixedMoment B raw19725step0 raw19725step0Labels = mixedMoment B raw19725step1 raw19725step1Labels := by
      have hz : ∀ j, raw19725step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19725step1 = (fun i j => raw19725step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19725step1 raw19725step0; decide +kernel
      have hl : raw19725step1Labels = raw19725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19725step0 raw19725step0Labels permutation56 hz
    mixedMoment B raw19725step1 raw19725step1Labels = mixedMoment B raw19725step2 raw19725step2Labels := by
      have ha : raw19725step2 = (fun i j => raw19725step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19725step2 raw19725step1; decide +kernel
      have hl : raw19725step2Labels = raw19725step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19725step1 raw19725step1Labels permutation31 permutation3
    mixedMoment B raw19725step2 raw19725step2Labels = mixedMoment B raw19725step3 raw19725step3Labels := by
      have ha : raw19725step3 = -raw19725step2 := by apply Matrix.ext; change ∀ i j, raw19725step3 i j = -(raw19725step2 i j); unfold raw19725step3 raw19725step2; decide +kernel
      have hl : raw19725step3Labels = raw19725step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19725step3 raw19725step3Labels = mixedMoment B raw19725step4 raw19725step4Labels := by
      have ha : raw19725step4 = raw19725step3 := by apply Matrix.ext; unfold raw19725step4 raw19725step3; decide +kernel
      have hl : raw19725step3Labels = labelEmbedding6 ∘ raw19725step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19725step3 raw19725step3Labels raw19725step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4108 node4108Labels := by rfl

def raw19726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19726step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19726step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19726step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19726step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19726 raw19726Labels = mixedMoment B node4108 node4108Labels := by
  calc
    mixedMoment B raw19726 raw19726Labels = mixedMoment B raw19726step0 raw19726step0Labels := by
      have hz : ∀ j, raw19726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19726step0 = (fun i j => raw19726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19726step0 raw19726; decide +kernel
      have hl : raw19726step0Labels = raw19726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19726 raw19726Labels permutation346 hz
    mixedMoment B raw19726step0 raw19726step0Labels = mixedMoment B raw19726step1 raw19726step1Labels := by
      have hz : ∀ j, raw19726step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19726step1 = (fun i j => raw19726step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19726step1 raw19726step0; decide +kernel
      have hl : raw19726step1Labels = raw19726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19726step0 raw19726step0Labels permutation56 hz
    mixedMoment B raw19726step1 raw19726step1Labels = mixedMoment B raw19726step2 raw19726step2Labels := by
      have ha : raw19726step2 = (fun i j => raw19726step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19726step2 raw19726step1; decide +kernel
      have hl : raw19726step2Labels = raw19726step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19726step1 raw19726step1Labels permutation31 permutation3
    mixedMoment B raw19726step2 raw19726step2Labels = mixedMoment B raw19726step3 raw19726step3Labels := by
      have ha : raw19726step3 = -raw19726step2 := by apply Matrix.ext; change ∀ i j, raw19726step3 i j = -(raw19726step2 i j); unfold raw19726step3 raw19726step2; decide +kernel
      have hl : raw19726step3Labels = raw19726step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19726step3 raw19726step3Labels = mixedMoment B raw19726step4 raw19726step4Labels := by
      have ha : raw19726step4 = raw19726step3 := by apply Matrix.ext; unfold raw19726step4 raw19726step3; decide +kernel
      have hl : raw19726step3Labels = labelEmbedding6 ∘ raw19726step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19726step3 raw19726step3Labels raw19726step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4108 node4108Labels := by rfl

def raw19727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19727step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![5, -4, -1]]
def raw19727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19727step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-1, -1, 2], ![-4, 2, 2]]
def raw19727step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19727step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw19727step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19727step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw19727step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19727 raw19727Labels = mixedMoment B node4134 node4134Labels := by
  calc
    mixedMoment B raw19727 raw19727Labels = mixedMoment B raw19727step0 raw19727step0Labels := by
      have hz : ∀ j, raw19727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19727step0 = (fun i j => raw19727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19727step0 raw19727; decide +kernel
      have hl : raw19727step0Labels = raw19727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19727 raw19727Labels permutation434 hz
    mixedMoment B raw19727step0 raw19727step0Labels = mixedMoment B raw19727step1 raw19727step1Labels := by
      have hz : ∀ j, raw19727step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19727step1 = (fun i j => raw19727step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19727step1 raw19727step0; decide +kernel
      have hl : raw19727step1Labels = raw19727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19727step0 raw19727step0Labels permutation80 hz
    mixedMoment B raw19727step1 raw19727step1Labels = mixedMoment B raw19727step2 raw19727step2Labels := by
      have hz : ∀ j, raw19727step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19727step2 = (fun i j => raw19727step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19727step2 raw19727step1; decide +kernel
      have hl : raw19727step2Labels = raw19727step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19727step1 raw19727step1Labels permutation14 hz
    mixedMoment B raw19727step2 raw19727step2Labels = mixedMoment B raw19727step3 raw19727step3Labels := by
      have ha : raw19727step3 = (fun i j => raw19727step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19727step3 raw19727step2; decide +kernel
      have hl : raw19727step3Labels = raw19727step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19727step2 raw19727step2Labels permutation7 permutation3
    mixedMoment B raw19727step3 raw19727step3Labels = mixedMoment B raw19727step4 raw19727step4Labels := by
      have ha : raw19727step4 = -raw19727step3 := by apply Matrix.ext; change ∀ i j, raw19727step4 i j = -(raw19727step3 i j); unfold raw19727step4 raw19727step3; decide +kernel
      have hl : raw19727step4Labels = raw19727step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19727step4 raw19727step4Labels = mixedMoment B raw19727step5 raw19727step5Labels := by
      have ha : raw19727step5 = raw19727step4 := by apply Matrix.ext; unfold raw19727step5 raw19727step4; decide +kernel
      have hl : raw19727step4Labels = labelEmbedding6 ∘ raw19727step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19727step4 raw19727step4Labels raw19727step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4134 node4134Labels := by rfl

def raw19728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw19728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw19728step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw19728step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19728step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw19728step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19728step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw19728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19728step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw19728step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19728 raw19728Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw19728 raw19728Labels = mixedMoment B raw19728step0 raw19728step0Labels := by
      have hz : ∀ j, raw19728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19728step0 = (fun i j => raw19728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19728step0 raw19728; decide +kernel
      have hl : raw19728step0Labels = raw19728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19728 raw19728Labels permutation434 hz
    mixedMoment B raw19728step0 raw19728step0Labels = mixedMoment B raw19728step1 raw19728step1Labels := by
      have hz : ∀ j, raw19728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19728step1 = (fun i j => raw19728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19728step1 raw19728step0; decide +kernel
      have hl : raw19728step1Labels = raw19728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19728step0 raw19728step0Labels permutation80 hz
    mixedMoment B raw19728step1 raw19728step1Labels = mixedMoment B raw19728step2 raw19728step2Labels := by
      have hz : ∀ j, raw19728step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19728step2 = (fun i j => raw19728step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19728step2 raw19728step1; decide +kernel
      have hl : raw19728step2Labels = raw19728step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19728step1 raw19728step1Labels permutation14 hz
    mixedMoment B raw19728step2 raw19728step2Labels = mixedMoment B raw19728step3 raw19728step3Labels := by
      have ha : raw19728step3 = (fun i j => raw19728step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19728step3 raw19728step2; decide +kernel
      have hl : raw19728step3Labels = raw19728step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19728step2 raw19728step2Labels permutation7 permutation3
    mixedMoment B raw19728step3 raw19728step3Labels = mixedMoment B raw19728step4 raw19728step4Labels := by
      have ha : raw19728step4 = -raw19728step3 := by apply Matrix.ext; change ∀ i j, raw19728step4 i j = -(raw19728step3 i j); unfold raw19728step4 raw19728step3; decide +kernel
      have hl : raw19728step4Labels = raw19728step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw19729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19729step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19729step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19729 raw19729Labels = mixedMoment B node574 node574Labels := by
  calc
    mixedMoment B raw19729 raw19729Labels = mixedMoment B raw19729step0 raw19729step0Labels := by
      have hz : ∀ j, raw19729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19729step0 = (fun i j => raw19729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19729step0 raw19729; decide +kernel
      have hl : raw19729step0Labels = raw19729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19729 raw19729Labels permutation434 hz
    mixedMoment B raw19729step0 raw19729step0Labels = mixedMoment B raw19729step1 raw19729step1Labels := by
      have hz : ∀ j, raw19729step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19729step1 = (fun i j => raw19729step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19729step1 raw19729step0; decide +kernel
      have hl : raw19729step1Labels = raw19729step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19729step0 raw19729step0Labels permutation80 hz
    mixedMoment B raw19729step1 raw19729step1Labels = mixedMoment B raw19729step2 raw19729step2Labels := by
      have ha : raw19729step2 = (fun i j => raw19729step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19729step2 raw19729step1; decide +kernel
      have hl : raw19729step2Labels = raw19729step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19729step1 raw19729step1Labels permutation10 permutation3
    _ = mixedMoment B node574 node574Labels := by rfl

def raw19730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19730 raw19730Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw19730 raw19730Labels = mixedMoment B raw19730step0 raw19730step0Labels := by
      have hz : ∀ j, raw19730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19730step0 = (fun i j => raw19730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19730step0 raw19730; decide +kernel
      have hl : raw19730step0Labels = raw19730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19730 raw19730Labels permutation434 hz
    mixedMoment B raw19730step0 raw19730step0Labels = mixedMoment B raw19730step1 raw19730step1Labels := by
      have ha : raw19730step1 = (fun i j => raw19730step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19730step1 raw19730step0; decide +kernel
      have hl : raw19730step1Labels = raw19730step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19730step0 raw19730step0Labels permutation139 permutation3
    mixedMoment B raw19730step1 raw19730step1Labels = mixedMoment B raw19730step2 raw19730step2Labels := by
      have ha : raw19730step2 = -raw19730step1 := by apply Matrix.ext; change ∀ i j, raw19730step2 i j = -(raw19730step1 i j); unfold raw19730step2 raw19730step1; decide +kernel
      have hl : raw19730step2Labels = raw19730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node871 node871Labels := by rfl

def raw19731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19731 raw19731Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw19731 raw19731Labels = mixedMoment B raw19731step0 raw19731step0Labels := by
      have hz : ∀ j, raw19731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19731step0 = (fun i j => raw19731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19731step0 raw19731; decide +kernel
      have hl : raw19731step0Labels = raw19731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19731 raw19731Labels permutation346 hz
    mixedMoment B raw19731step0 raw19731step0Labels = mixedMoment B raw19731step1 raw19731step1Labels := by
      have ha : raw19731step1 = (fun i j => raw19731step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19731step1 raw19731step0; decide +kernel
      have hl : raw19731step1Labels = raw19731step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19731step0 raw19731step0Labels permutation139 permutation3
    mixedMoment B raw19731step1 raw19731step1Labels = mixedMoment B raw19731step2 raw19731step2Labels := by
      have ha : raw19731step2 = -raw19731step1 := by apply Matrix.ext; change ∀ i j, raw19731step2 i j = -(raw19731step1 i j); unfold raw19731step2 raw19731step1; decide +kernel
      have hl : raw19731step2Labels = raw19731step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node871 node871Labels := by rfl

def raw19732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19732step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19732step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19732step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19732 raw19732Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw19732 raw19732Labels = mixedMoment B raw19732step0 raw19732step0Labels := by
      have hz : ∀ j, raw19732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19732step0 = (fun i j => raw19732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19732step0 raw19732; decide +kernel
      have hl : raw19732step0Labels = raw19732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19732 raw19732Labels permutation434 hz
    mixedMoment B raw19732step0 raw19732step0Labels = mixedMoment B raw19732step1 raw19732step1Labels := by
      have hz : ∀ j, raw19732step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19732step1 = (fun i j => raw19732step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19732step1 raw19732step0; decide +kernel
      have hl : raw19732step1Labels = raw19732step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19732step0 raw19732step0Labels permutation80 hz
    mixedMoment B raw19732step1 raw19732step1Labels = mixedMoment B raw19732step2 raw19732step2Labels := by
      have ha : raw19732step2 = (fun i j => raw19732step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19732step2 raw19732step1; decide +kernel
      have hl : raw19732step2Labels = raw19732step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19732step1 raw19732step1Labels permutation29 permutation3
    mixedMoment B raw19732step2 raw19732step2Labels = mixedMoment B raw19732step3 raw19732step3Labels := by
      have ha : raw19732step3 = -raw19732step2 := by apply Matrix.ext; change ∀ i j, raw19732step3 i j = -(raw19732step2 i j); unfold raw19732step3 raw19732step2; decide +kernel
      have hl : raw19732step3Labels = raw19732step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node893 node893Labels := by rfl

def raw19733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19733step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19733 raw19733Labels = mixedMoment B node574 node574Labels := by
  calc
    mixedMoment B raw19733 raw19733Labels = mixedMoment B raw19733step0 raw19733step0Labels := by
      have hz : ∀ j, raw19733 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19733step0 = (fun i j => raw19733 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19733step0 raw19733; decide +kernel
      have hl : raw19733step0Labels = raw19733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19733 raw19733Labels permutation434 hz
    mixedMoment B raw19733step0 raw19733step0Labels = mixedMoment B raw19733step1 raw19733step1Labels := by
      have hz : ∀ j, raw19733step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19733step1 = (fun i j => raw19733step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19733step1 raw19733step0; decide +kernel
      have hl : raw19733step1Labels = raw19733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19733step0 raw19733step0Labels permutation56 hz
    mixedMoment B raw19733step1 raw19733step1Labels = mixedMoment B raw19733step2 raw19733step2Labels := by
      have ha : raw19733step2 = (fun i j => raw19733step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19733step2 raw19733step1; decide +kernel
      have hl : raw19733step2Labels = raw19733step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19733step1 raw19733step1Labels permutation10 permutation3
    _ = mixedMoment B node574 node574Labels := by rfl

def raw19734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19734step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19734 raw19734Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw19734 raw19734Labels = mixedMoment B raw19734step0 raw19734step0Labels := by
      have hz : ∀ j, raw19734 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19734step0 = (fun i j => raw19734 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19734step0 raw19734; decide +kernel
      have hl : raw19734step0Labels = raw19734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19734 raw19734Labels permutation434 hz
    mixedMoment B raw19734step0 raw19734step0Labels = mixedMoment B raw19734step1 raw19734step1Labels := by
      have ha : raw19734step1 = (fun i j => raw19734step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19734step1 raw19734step0; decide +kernel
      have hl : raw19734step1Labels = raw19734step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19734step0 raw19734step0Labels permutation145 permutation3
    mixedMoment B raw19734step1 raw19734step1Labels = mixedMoment B raw19734step2 raw19734step2Labels := by
      have ha : raw19734step2 = -raw19734step1 := by apply Matrix.ext; change ∀ i j, raw19734step2 i j = -(raw19734step1 i j); unfold raw19734step2 raw19734step1; decide +kernel
      have hl : raw19734step2Labels = raw19734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node871 node871Labels := by rfl

def raw19735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19735step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19735 raw19735Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw19735 raw19735Labels = mixedMoment B raw19735step0 raw19735step0Labels := by
      have hz : ∀ j, raw19735 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19735step0 = (fun i j => raw19735 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19735step0 raw19735; decide +kernel
      have hl : raw19735step0Labels = raw19735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19735 raw19735Labels permutation265 hz
    mixedMoment B raw19735step0 raw19735step0Labels = mixedMoment B raw19735step1 raw19735step1Labels := by
      have ha : raw19735step1 = (fun i j => raw19735step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19735step1 raw19735step0; decide +kernel
      have hl : raw19735step1Labels = raw19735step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19735step0 raw19735step0Labels permutation139 permutation3
    mixedMoment B raw19735step1 raw19735step1Labels = mixedMoment B raw19735step2 raw19735step2Labels := by
      have ha : raw19735step2 = -raw19735step1 := by apply Matrix.ext; change ∀ i j, raw19735step2 i j = -(raw19735step1 i j); unfold raw19735step2 raw19735step1; decide +kernel
      have hl : raw19735step2Labels = raw19735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node871 node871Labels := by rfl

def raw19736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19736step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19736 raw19736Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw19736 raw19736Labels = mixedMoment B raw19736step0 raw19736step0Labels := by
      have hz : ∀ j, raw19736 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19736step0 = (fun i j => raw19736 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19736step0 raw19736; decide +kernel
      have hl : raw19736step0Labels = raw19736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19736 raw19736Labels permutation434 hz
    mixedMoment B raw19736step0 raw19736step0Labels = mixedMoment B raw19736step1 raw19736step1Labels := by
      have hz : ∀ j, raw19736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19736step1 = (fun i j => raw19736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19736step1 raw19736step0; decide +kernel
      have hl : raw19736step1Labels = raw19736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19736step0 raw19736step0Labels permutation56 hz
    mixedMoment B raw19736step1 raw19736step1Labels = mixedMoment B raw19736step2 raw19736step2Labels := by
      have ha : raw19736step2 = (fun i j => raw19736step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19736step2 raw19736step1; decide +kernel
      have hl : raw19736step2Labels = raw19736step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19736step1 raw19736step1Labels permutation29 permutation3
    mixedMoment B raw19736step2 raw19736step2Labels = mixedMoment B raw19736step3 raw19736step3Labels := by
      have ha : raw19736step3 = -raw19736step2 := by apply Matrix.ext; change ∀ i j, raw19736step3 i j = -(raw19736step2 i j); unfold raw19736step3 raw19736step2; decide +kernel
      have hl : raw19736step3Labels = raw19736step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node893 node893Labels := by rfl

def raw19737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19737step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19737step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19737 raw19737Labels = mixedMoment B node574 node574Labels := by
  calc
    mixedMoment B raw19737 raw19737Labels = mixedMoment B raw19737step0 raw19737step0Labels := by
      have hz : ∀ j, raw19737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19737step0 = (fun i j => raw19737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19737step0 raw19737; decide +kernel
      have hl : raw19737step0Labels = raw19737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19737 raw19737Labels permutation346 hz
    mixedMoment B raw19737step0 raw19737step0Labels = mixedMoment B raw19737step1 raw19737step1Labels := by
      have hz : ∀ j, raw19737step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19737step1 = (fun i j => raw19737step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19737step1 raw19737step0; decide +kernel
      have hl : raw19737step1Labels = raw19737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19737step0 raw19737step0Labels permutation56 hz
    mixedMoment B raw19737step1 raw19737step1Labels = mixedMoment B raw19737step2 raw19737step2Labels := by
      have ha : raw19737step2 = (fun i j => raw19737step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19737step2 raw19737step1; decide +kernel
      have hl : raw19737step2Labels = raw19737step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19737step1 raw19737step1Labels permutation10 permutation3
    _ = mixedMoment B node574 node574Labels := by rfl

def raw19738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19738step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19738 raw19738Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw19738 raw19738Labels = mixedMoment B raw19738step0 raw19738step0Labels := by
      have hz : ∀ j, raw19738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19738step0 = (fun i j => raw19738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19738step0 raw19738; decide +kernel
      have hl : raw19738step0Labels = raw19738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19738 raw19738Labels permutation346 hz
    mixedMoment B raw19738step0 raw19738step0Labels = mixedMoment B raw19738step1 raw19738step1Labels := by
      have ha : raw19738step1 = (fun i j => raw19738step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19738step1 raw19738step0; decide +kernel
      have hl : raw19738step1Labels = raw19738step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19738step0 raw19738step0Labels permutation145 permutation3
    mixedMoment B raw19738step1 raw19738step1Labels = mixedMoment B raw19738step2 raw19738step2Labels := by
      have ha : raw19738step2 = -raw19738step1 := by apply Matrix.ext; change ∀ i j, raw19738step2 i j = -(raw19738step1 i j); unfold raw19738step2 raw19738step1; decide +kernel
      have hl : raw19738step2Labels = raw19738step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node871 node871Labels := by rfl

def raw19739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19739step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19739 raw19739Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw19739 raw19739Labels = mixedMoment B raw19739step0 raw19739step0Labels := by
      have hz : ∀ j, raw19739 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19739step0 = (fun i j => raw19739 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19739step0 raw19739; decide +kernel
      have hl : raw19739step0Labels = raw19739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19739 raw19739Labels permutation265 hz
    mixedMoment B raw19739step0 raw19739step0Labels = mixedMoment B raw19739step1 raw19739step1Labels := by
      have ha : raw19739step1 = (fun i j => raw19739step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19739step1 raw19739step0; decide +kernel
      have hl : raw19739step1Labels = raw19739step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19739step0 raw19739step0Labels permutation145 permutation3
    mixedMoment B raw19739step1 raw19739step1Labels = mixedMoment B raw19739step2 raw19739step2Labels := by
      have ha : raw19739step2 = -raw19739step1 := by apply Matrix.ext; change ∀ i j, raw19739step2 i j = -(raw19739step1 i j); unfold raw19739step2 raw19739step1; decide +kernel
      have hl : raw19739step2Labels = raw19739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node871 node871Labels := by rfl

def raw19740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19740step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19740step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19740step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19740step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19740step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19740 raw19740Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw19740 raw19740Labels = mixedMoment B raw19740step0 raw19740step0Labels := by
      have hz : ∀ j, raw19740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19740step0 = (fun i j => raw19740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19740step0 raw19740; decide +kernel
      have hl : raw19740step0Labels = raw19740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19740 raw19740Labels permutation346 hz
    mixedMoment B raw19740step0 raw19740step0Labels = mixedMoment B raw19740step1 raw19740step1Labels := by
      have hz : ∀ j, raw19740step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19740step1 = (fun i j => raw19740step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19740step1 raw19740step0; decide +kernel
      have hl : raw19740step1Labels = raw19740step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19740step0 raw19740step0Labels permutation56 hz
    mixedMoment B raw19740step1 raw19740step1Labels = mixedMoment B raw19740step2 raw19740step2Labels := by
      have ha : raw19740step2 = (fun i j => raw19740step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19740step2 raw19740step1; decide +kernel
      have hl : raw19740step2Labels = raw19740step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19740step1 raw19740step1Labels permutation29 permutation3
    mixedMoment B raw19740step2 raw19740step2Labels = mixedMoment B raw19740step3 raw19740step3Labels := by
      have ha : raw19740step3 = -raw19740step2 := by apply Matrix.ext; change ∀ i j, raw19740step3 i j = -(raw19740step2 i j); unfold raw19740step3 raw19740step2; decide +kernel
      have hl : raw19740step3Labels = raw19740step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node893 node893Labels := by rfl

def raw19741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19741step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19741step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19741step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![4, -3, -1]]
def raw19741step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19741step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19741 raw19741Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw19741 raw19741Labels = mixedMoment B raw19741step0 raw19741step0Labels := by
      have hz : ∀ j, raw19741 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19741step0 = (fun i j => raw19741 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19741step0 raw19741; decide +kernel
      have hl : raw19741step0Labels = raw19741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19741 raw19741Labels permutation434 hz
    mixedMoment B raw19741step0 raw19741step0Labels = mixedMoment B raw19741step1 raw19741step1Labels := by
      have hz : ∀ j, raw19741step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19741step1 = (fun i j => raw19741step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19741step1 raw19741step0; decide +kernel
      have hl : raw19741step1Labels = raw19741step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19741step0 raw19741step0Labels permutation80 hz
    mixedMoment B raw19741step1 raw19741step1Labels = mixedMoment B raw19741step2 raw19741step2Labels := by
      have hz : ∀ j, raw19741step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19741step2 = (fun i j => raw19741step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19741step2 raw19741step1; decide +kernel
      have hl : raw19741step2Labels = raw19741step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19741step1 raw19741step1Labels permutation14 hz
    mixedMoment B raw19741step2 raw19741step2Labels = mixedMoment B raw19741step3 raw19741step3Labels := by
      have ha : raw19741step3 = (fun i j => raw19741step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19741step3 raw19741step2; decide +kernel
      have hl : raw19741step3Labels = raw19741step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19741step2 raw19741step2Labels permutation2 permutation3
    _ = mixedMoment B node609 node609Labels := by rfl

def raw19742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19742step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19742step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19742step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19742step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19742 raw19742Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw19742 raw19742Labels = mixedMoment B raw19742step0 raw19742step0Labels := by
      have hz : ∀ j, raw19742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19742step0 = (fun i j => raw19742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19742step0 raw19742; decide +kernel
      have hl : raw19742step0Labels = raw19742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19742 raw19742Labels permutation434 hz
    mixedMoment B raw19742step0 raw19742step0Labels = mixedMoment B raw19742step1 raw19742step1Labels := by
      have hz : ∀ j, raw19742step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19742step1 = (fun i j => raw19742step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19742step1 raw19742step0; decide +kernel
      have hl : raw19742step1Labels = raw19742step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19742step0 raw19742step0Labels permutation80 hz
    mixedMoment B raw19742step1 raw19742step1Labels = mixedMoment B raw19742step2 raw19742step2Labels := by
      have ha : raw19742step2 = (fun i j => raw19742step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19742step2 raw19742step1; decide +kernel
      have hl : raw19742step2Labels = raw19742step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19742step1 raw19742step1Labels permutation31 permutation3
    mixedMoment B raw19742step2 raw19742step2Labels = mixedMoment B raw19742step3 raw19742step3Labels := by
      have ha : raw19742step3 = -raw19742step2 := by apply Matrix.ext; change ∀ i j, raw19742step3 i j = -(raw19742step2 i j); unfold raw19742step3 raw19742step2; decide +kernel
      have hl : raw19742step3Labels = raw19742step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

def raw19743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19743step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19743step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19743step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19743 raw19743Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw19743 raw19743Labels = mixedMoment B raw19743step0 raw19743step0Labels := by
      have hz : ∀ j, raw19743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19743step0 = (fun i j => raw19743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19743step0 raw19743; decide +kernel
      have hl : raw19743step0Labels = raw19743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19743 raw19743Labels permutation434 hz
    mixedMoment B raw19743step0 raw19743step0Labels = mixedMoment B raw19743step1 raw19743step1Labels := by
      have hz : ∀ j, raw19743step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19743step1 = (fun i j => raw19743step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19743step1 raw19743step0; decide +kernel
      have hl : raw19743step1Labels = raw19743step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19743step0 raw19743step0Labels permutation56 hz
    mixedMoment B raw19743step1 raw19743step1Labels = mixedMoment B raw19743step2 raw19743step2Labels := by
      have ha : raw19743step2 = (fun i j => raw19743step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19743step2 raw19743step1; decide +kernel
      have hl : raw19743step2Labels = raw19743step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19743step1 raw19743step1Labels permutation31 permutation3
    mixedMoment B raw19743step2 raw19743step2Labels = mixedMoment B raw19743step3 raw19743step3Labels := by
      have ha : raw19743step3 = -raw19743step2 := by apply Matrix.ext; change ∀ i j, raw19743step3 i j = -(raw19743step2 i j); unfold raw19743step3 raw19743step2; decide +kernel
      have hl : raw19743step3Labels = raw19743step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

def raw19744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19744step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19744step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19744step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19744step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19744 raw19744Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw19744 raw19744Labels = mixedMoment B raw19744step0 raw19744step0Labels := by
      have hz : ∀ j, raw19744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19744step0 = (fun i j => raw19744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19744step0 raw19744; decide +kernel
      have hl : raw19744step0Labels = raw19744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19744 raw19744Labels permutation346 hz
    mixedMoment B raw19744step0 raw19744step0Labels = mixedMoment B raw19744step1 raw19744step1Labels := by
      have hz : ∀ j, raw19744step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19744step1 = (fun i j => raw19744step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19744step1 raw19744step0; decide +kernel
      have hl : raw19744step1Labels = raw19744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19744step0 raw19744step0Labels permutation56 hz
    mixedMoment B raw19744step1 raw19744step1Labels = mixedMoment B raw19744step2 raw19744step2Labels := by
      have ha : raw19744step2 = (fun i j => raw19744step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19744step2 raw19744step1; decide +kernel
      have hl : raw19744step2Labels = raw19744step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19744step1 raw19744step1Labels permutation31 permutation3
    mixedMoment B raw19744step2 raw19744step2Labels = mixedMoment B raw19744step3 raw19744step3Labels := by
      have ha : raw19744step3 = -raw19744step2 := by apply Matrix.ext; change ∀ i j, raw19744step3 i j = -(raw19744step2 i j); unfold raw19744step3 raw19744step2; decide +kernel
      have hl : raw19744step3Labels = raw19744step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

def raw19745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19745step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19745step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19745step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![5, -4, -1]]
def raw19745step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19745step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-5, 2, 3]]
def raw19745step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19745step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw19745step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19745 raw19745Labels = mixedMoment B node549 node549Labels := by
  calc
    mixedMoment B raw19745 raw19745Labels = mixedMoment B raw19745step0 raw19745step0Labels := by
      have hz : ∀ j, raw19745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19745step0 = (fun i j => raw19745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19745step0 raw19745; decide +kernel
      have hl : raw19745step0Labels = raw19745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19745 raw19745Labels permutation434 hz
    mixedMoment B raw19745step0 raw19745step0Labels = mixedMoment B raw19745step1 raw19745step1Labels := by
      have hz : ∀ j, raw19745step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19745step1 = (fun i j => raw19745step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19745step1 raw19745step0; decide +kernel
      have hl : raw19745step1Labels = raw19745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19745step0 raw19745step0Labels permutation80 hz
    mixedMoment B raw19745step1 raw19745step1Labels = mixedMoment B raw19745step2 raw19745step2Labels := by
      have hz : ∀ j, raw19745step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19745step2 = (fun i j => raw19745step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19745step2 raw19745step1; decide +kernel
      have hl : raw19745step2Labels = raw19745step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19745step1 raw19745step1Labels permutation14 hz
    mixedMoment B raw19745step2 raw19745step2Labels = mixedMoment B raw19745step3 raw19745step3Labels := by
      have ha : raw19745step3 = (fun i j => raw19745step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19745step3 raw19745step2; decide +kernel
      have hl : raw19745step3Labels = raw19745step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19745step2 raw19745step2Labels permutation7 permutation3
    mixedMoment B raw19745step3 raw19745step3Labels = mixedMoment B raw19745step4 raw19745step4Labels := by
      have ha : raw19745step4 = -raw19745step3 := by apply Matrix.ext; change ∀ i j, raw19745step4 i j = -(raw19745step3 i j); unfold raw19745step4 raw19745step3; decide +kernel
      have hl : raw19745step4Labels = raw19745step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node549 node549Labels := by rfl

def raw19746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19746step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19746step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19746step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19746step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19746 raw19746Labels = mixedMoment B node545 node545Labels := by
  calc
    mixedMoment B raw19746 raw19746Labels = mixedMoment B raw19746step0 raw19746step0Labels := by
      have hz : ∀ j, raw19746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19746step0 = (fun i j => raw19746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19746step0 raw19746; decide +kernel
      have hl : raw19746step0Labels = raw19746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19746 raw19746Labels permutation434 hz
    mixedMoment B raw19746step0 raw19746step0Labels = mixedMoment B raw19746step1 raw19746step1Labels := by
      have hz : ∀ j, raw19746step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19746step1 = (fun i j => raw19746step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19746step1 raw19746step0; decide +kernel
      have hl : raw19746step1Labels = raw19746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19746step0 raw19746step0Labels permutation80 hz
    mixedMoment B raw19746step1 raw19746step1Labels = mixedMoment B raw19746step2 raw19746step2Labels := by
      have ha : raw19746step2 = (fun i j => raw19746step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19746step2 raw19746step1; decide +kernel
      have hl : raw19746step2Labels = raw19746step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19746step1 raw19746step1Labels permutation31 permutation3
    mixedMoment B raw19746step2 raw19746step2Labels = mixedMoment B raw19746step3 raw19746step3Labels := by
      have ha : raw19746step3 = -raw19746step2 := by apply Matrix.ext; change ∀ i j, raw19746step3 i j = -(raw19746step2 i j); unfold raw19746step3 raw19746step2; decide +kernel
      have hl : raw19746step3Labels = raw19746step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node545 node545Labels := by rfl

def raw19747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19747step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19747step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19747step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19747step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19747 raw19747Labels = mixedMoment B node545 node545Labels := by
  calc
    mixedMoment B raw19747 raw19747Labels = mixedMoment B raw19747step0 raw19747step0Labels := by
      have hz : ∀ j, raw19747 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19747step0 = (fun i j => raw19747 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19747step0 raw19747; decide +kernel
      have hl : raw19747step0Labels = raw19747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19747 raw19747Labels permutation434 hz
    mixedMoment B raw19747step0 raw19747step0Labels = mixedMoment B raw19747step1 raw19747step1Labels := by
      have hz : ∀ j, raw19747step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19747step1 = (fun i j => raw19747step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19747step1 raw19747step0; decide +kernel
      have hl : raw19747step1Labels = raw19747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19747step0 raw19747step0Labels permutation56 hz
    mixedMoment B raw19747step1 raw19747step1Labels = mixedMoment B raw19747step2 raw19747step2Labels := by
      have ha : raw19747step2 = (fun i j => raw19747step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19747step2 raw19747step1; decide +kernel
      have hl : raw19747step2Labels = raw19747step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19747step1 raw19747step1Labels permutation31 permutation3
    mixedMoment B raw19747step2 raw19747step2Labels = mixedMoment B raw19747step3 raw19747step3Labels := by
      have ha : raw19747step3 = -raw19747step2 := by apply Matrix.ext; change ∀ i j, raw19747step3 i j = -(raw19747step2 i j); unfold raw19747step3 raw19747step2; decide +kernel
      have hl : raw19747step3Labels = raw19747step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node545 node545Labels := by rfl

def raw19748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19748step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![5, -4, -1]]
def raw19748step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19748 raw19748Labels = mixedMoment B node545 node545Labels := by
  calc
    mixedMoment B raw19748 raw19748Labels = mixedMoment B raw19748step0 raw19748step0Labels := by
      have hz : ∀ j, raw19748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19748step0 = (fun i j => raw19748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19748step0 raw19748; decide +kernel
      have hl : raw19748step0Labels = raw19748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19748 raw19748Labels permutation346 hz
    mixedMoment B raw19748step0 raw19748step0Labels = mixedMoment B raw19748step1 raw19748step1Labels := by
      have hz : ∀ j, raw19748step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19748step1 = (fun i j => raw19748step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19748step1 raw19748step0; decide +kernel
      have hl : raw19748step1Labels = raw19748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19748step0 raw19748step0Labels permutation56 hz
    mixedMoment B raw19748step1 raw19748step1Labels = mixedMoment B raw19748step2 raw19748step2Labels := by
      have ha : raw19748step2 = (fun i j => raw19748step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19748step2 raw19748step1; decide +kernel
      have hl : raw19748step2Labels = raw19748step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19748step1 raw19748step1Labels permutation31 permutation3
    mixedMoment B raw19748step2 raw19748step2Labels = mixedMoment B raw19748step3 raw19748step3Labels := by
      have ha : raw19748step3 = -raw19748step2 := by apply Matrix.ext; change ∀ i j, raw19748step3 i j = -(raw19748step2 i j); unfold raw19748step3 raw19748step2; decide +kernel
      have hl : raw19748step3Labels = raw19748step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node545 node545Labels := by rfl

def raw19749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19749step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![5, -4, -1]]
def raw19749step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19749step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![5, -4, -1]]
def raw19749step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19749step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-1, -1, 2], ![-4, 2, 2]]
def raw19749step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19749step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw19749step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19749 raw19749Labels = mixedMoment B node564 node564Labels := by
  calc
    mixedMoment B raw19749 raw19749Labels = mixedMoment B raw19749step0 raw19749step0Labels := by
      have hz : ∀ j, raw19749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19749step0 = (fun i j => raw19749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19749step0 raw19749; decide +kernel
      have hl : raw19749step0Labels = raw19749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19749 raw19749Labels permutation434 hz
    mixedMoment B raw19749step0 raw19749step0Labels = mixedMoment B raw19749step1 raw19749step1Labels := by
      have hz : ∀ j, raw19749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19749step1 = (fun i j => raw19749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19749step1 raw19749step0; decide +kernel
      have hl : raw19749step1Labels = raw19749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19749step0 raw19749step0Labels permutation80 hz
    mixedMoment B raw19749step1 raw19749step1Labels = mixedMoment B raw19749step2 raw19749step2Labels := by
      have hz : ∀ j, raw19749step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19749step2 = (fun i j => raw19749step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19749step2 raw19749step1; decide +kernel
      have hl : raw19749step2Labels = raw19749step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19749step1 raw19749step1Labels permutation14 hz
    mixedMoment B raw19749step2 raw19749step2Labels = mixedMoment B raw19749step3 raw19749step3Labels := by
      have ha : raw19749step3 = (fun i j => raw19749step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19749step3 raw19749step2; decide +kernel
      have hl : raw19749step3Labels = raw19749step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19749step2 raw19749step2Labels permutation7 permutation3
    mixedMoment B raw19749step3 raw19749step3Labels = mixedMoment B raw19749step4 raw19749step4Labels := by
      have ha : raw19749step4 = -raw19749step3 := by apply Matrix.ext; change ∀ i j, raw19749step4 i j = -(raw19749step3 i j); unfold raw19749step4 raw19749step3; decide +kernel
      have hl : raw19749step4Labels = raw19749step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node564 node564Labels := by rfl

def raw19750 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw19750step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19750step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19750step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19750step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19750step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19750 raw19750Labels = mixedMoment B node4445 node4445Labels := by
  calc
    mixedMoment B raw19750 raw19750Labels = mixedMoment B raw19750step0 raw19750step0Labels := by
      have hz : ∀ j, raw19750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19750step0 = (fun i j => raw19750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19750step0 raw19750; decide +kernel
      have hl : raw19750step0Labels = raw19750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19750 raw19750Labels permutation434 hz
    mixedMoment B raw19750step0 raw19750step0Labels = mixedMoment B raw19750step1 raw19750step1Labels := by
      have hz : ∀ j, raw19750step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19750step1 = (fun i j => raw19750step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19750step1 raw19750step0; decide +kernel
      have hl : raw19750step1Labels = raw19750step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19750step0 raw19750step0Labels permutation80 hz
    mixedMoment B raw19750step1 raw19750step1Labels = mixedMoment B raw19750step2 raw19750step2Labels := by
      have ha : raw19750step2 = (fun i j => raw19750step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19750step2 raw19750step1; decide +kernel
      have hl : raw19750step2Labels = raw19750step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19750step1 raw19750step1Labels permutation29 permutation6
    mixedMoment B raw19750step2 raw19750step2Labels = mixedMoment B raw19750step3 raw19750step3Labels := by
      have ha : raw19750step3 = -raw19750step2 := by apply Matrix.ext; change ∀ i j, raw19750step3 i j = -(raw19750step2 i j); unfold raw19750step3 raw19750step2; decide +kernel
      have hl : raw19750step3Labels = raw19750step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19750step3 raw19750step3Labels = mixedMoment B raw19750step4 raw19750step4Labels := by
      have ha : raw19750step4 = raw19750step3 := by apply Matrix.ext; unfold raw19750step4 raw19750step3; decide +kernel
      have hl : raw19750step3Labels = labelEmbedding9 ∘ raw19750step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19750step3 raw19750step3Labels raw19750step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4445 node4445Labels := by rfl

def raw19751 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw19751step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19751step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19751step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19751step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19751step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19751 raw19751Labels = mixedMoment B node4445 node4445Labels := by
  calc
    mixedMoment B raw19751 raw19751Labels = mixedMoment B raw19751step0 raw19751step0Labels := by
      have hz : ∀ j, raw19751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19751step0 = (fun i j => raw19751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19751step0 raw19751; decide +kernel
      have hl : raw19751step0Labels = raw19751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19751 raw19751Labels permutation434 hz
    mixedMoment B raw19751step0 raw19751step0Labels = mixedMoment B raw19751step1 raw19751step1Labels := by
      have hz : ∀ j, raw19751step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19751step1 = (fun i j => raw19751step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19751step1 raw19751step0; decide +kernel
      have hl : raw19751step1Labels = raw19751step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19751step0 raw19751step0Labels permutation56 hz
    mixedMoment B raw19751step1 raw19751step1Labels = mixedMoment B raw19751step2 raw19751step2Labels := by
      have ha : raw19751step2 = (fun i j => raw19751step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19751step2 raw19751step1; decide +kernel
      have hl : raw19751step2Labels = raw19751step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19751step1 raw19751step1Labels permutation29 permutation6
    mixedMoment B raw19751step2 raw19751step2Labels = mixedMoment B raw19751step3 raw19751step3Labels := by
      have ha : raw19751step3 = -raw19751step2 := by apply Matrix.ext; change ∀ i j, raw19751step3 i j = -(raw19751step2 i j); unfold raw19751step3 raw19751step2; decide +kernel
      have hl : raw19751step3Labels = raw19751step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19751step3 raw19751step3Labels = mixedMoment B raw19751step4 raw19751step4Labels := by
      have ha : raw19751step4 = raw19751step3 := by apply Matrix.ext; unfold raw19751step4 raw19751step3; decide +kernel
      have hl : raw19751step3Labels = labelEmbedding9 ∘ raw19751step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19751step3 raw19751step3Labels raw19751step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4445 node4445Labels := by rfl

def raw19752 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw19752step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19752step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19752step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19752step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19752step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19752 raw19752Labels = mixedMoment B node4445 node4445Labels := by
  calc
    mixedMoment B raw19752 raw19752Labels = mixedMoment B raw19752step0 raw19752step0Labels := by
      have hz : ∀ j, raw19752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19752step0 = (fun i j => raw19752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19752step0 raw19752; decide +kernel
      have hl : raw19752step0Labels = raw19752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19752 raw19752Labels permutation346 hz
    mixedMoment B raw19752step0 raw19752step0Labels = mixedMoment B raw19752step1 raw19752step1Labels := by
      have hz : ∀ j, raw19752step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19752step1 = (fun i j => raw19752step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19752step1 raw19752step0; decide +kernel
      have hl : raw19752step1Labels = raw19752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19752step0 raw19752step0Labels permutation56 hz
    mixedMoment B raw19752step1 raw19752step1Labels = mixedMoment B raw19752step2 raw19752step2Labels := by
      have ha : raw19752step2 = (fun i j => raw19752step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19752step2 raw19752step1; decide +kernel
      have hl : raw19752step2Labels = raw19752step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19752step1 raw19752step1Labels permutation29 permutation6
    mixedMoment B raw19752step2 raw19752step2Labels = mixedMoment B raw19752step3 raw19752step3Labels := by
      have ha : raw19752step3 = -raw19752step2 := by apply Matrix.ext; change ∀ i j, raw19752step3 i j = -(raw19752step2 i j); unfold raw19752step3 raw19752step2; decide +kernel
      have hl : raw19752step3Labels = raw19752step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19752step3 raw19752step3Labels = mixedMoment B raw19752step4 raw19752step4Labels := by
      have ha : raw19752step4 = raw19752step3 := by apply Matrix.ext; unfold raw19752step4 raw19752step3; decide +kernel
      have hl : raw19752step3Labels = labelEmbedding9 ∘ raw19752step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19752step3 raw19752step3Labels raw19752step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4445 node4445Labels := by rfl

def raw19753 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19753step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, -3, 4]]
def raw19753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19753step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-4, 3, 1]]
def raw19753step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19753step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw19753step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19753step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw19753step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19753 raw19753Labels = mixedMoment B node4481 node4481Labels := by
  calc
    mixedMoment B raw19753 raw19753Labels = mixedMoment B raw19753step0 raw19753step0Labels := by
      have hz : ∀ j, raw19753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19753step0 = (fun i j => raw19753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19753step0 raw19753; decide +kernel
      have hl : raw19753step0Labels = raw19753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19753 raw19753Labels permutation434 hz
    mixedMoment B raw19753step0 raw19753step0Labels = mixedMoment B raw19753step1 raw19753step1Labels := by
      have hz : ∀ j, raw19753step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19753step1 = (fun i j => raw19753step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19753step1 raw19753step0; decide +kernel
      have hl : raw19753step1Labels = raw19753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19753step0 raw19753step0Labels permutation80 hz
    mixedMoment B raw19753step1 raw19753step1Labels = mixedMoment B raw19753step2 raw19753step2Labels := by
      have hz : ∀ j, raw19753step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19753step2 = (fun i j => raw19753step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19753step2 raw19753step1; decide +kernel
      have hl : raw19753step2Labels = raw19753step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19753step1 raw19753step1Labels permutation14 hz
    mixedMoment B raw19753step2 raw19753step2Labels = mixedMoment B raw19753step3 raw19753step3Labels := by
      have ha : raw19753step3 = (fun i j => raw19753step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19753step3 raw19753step2; decide +kernel
      have hl : raw19753step3Labels = raw19753step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19753step2 raw19753step2Labels permutation7 permutation6
    mixedMoment B raw19753step3 raw19753step3Labels = mixedMoment B raw19753step4 raw19753step4Labels := by
      have ha : raw19753step4 = -raw19753step3 := by apply Matrix.ext; change ∀ i j, raw19753step4 i j = -(raw19753step3 i j); unfold raw19753step4 raw19753step3; decide +kernel
      have hl : raw19753step4Labels = raw19753step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19753step4 raw19753step4Labels = mixedMoment B raw19753step5 raw19753step5Labels := by
      have ha : raw19753step5 = raw19753step4 := by apply Matrix.ext; unfold raw19753step5 raw19753step4; decide +kernel
      have hl : raw19753step4Labels = labelEmbedding9 ∘ raw19753step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19753step4 raw19753step4Labels raw19753step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4481 node4481Labels := by rfl

def raw19754 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19754step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19754step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19754step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19754 raw19754Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19754 raw19754Labels = mixedMoment B raw19754step0 raw19754step0Labels := by
      have hz : ∀ j, raw19754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19754step0 = (fun i j => raw19754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19754step0 raw19754; decide +kernel
      have hl : raw19754step0Labels = raw19754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19754 raw19754Labels permutation434 hz
    mixedMoment B raw19754step0 raw19754step0Labels = mixedMoment B raw19754step1 raw19754step1Labels := by
      have hz : ∀ j, raw19754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19754step1 = (fun i j => raw19754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19754step1 raw19754step0; decide +kernel
      have hl : raw19754step1Labels = raw19754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19754step0 raw19754step0Labels permutation80 hz
    mixedMoment B raw19754step1 raw19754step1Labels = mixedMoment B raw19754step2 raw19754step2Labels := by
      have ha : raw19754step2 = (fun i j => raw19754step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19754step2 raw19754step1; decide +kernel
      have hl : raw19754step2Labels = raw19754step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19754step1 raw19754step1Labels permutation10 permutation6
    mixedMoment B raw19754step2 raw19754step2Labels = mixedMoment B raw19754step3 raw19754step3Labels := by
      have ha : raw19754step3 = raw19754step2 := by apply Matrix.ext; unfold raw19754step3 raw19754step2; decide +kernel
      have hl : raw19754step2Labels = labelEmbedding9 ∘ raw19754step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19754step2 raw19754step2Labels raw19754step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19755 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19755step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19755step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19755step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19755step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19755 raw19755Labels = mixedMoment B node4394 node4394Labels := by
  calc
    mixedMoment B raw19755 raw19755Labels = mixedMoment B raw19755step0 raw19755step0Labels := by
      have hz : ∀ j, raw19755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19755step0 = (fun i j => raw19755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19755step0 raw19755; decide +kernel
      have hl : raw19755step0Labels = raw19755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19755 raw19755Labels permutation434 hz
    mixedMoment B raw19755step0 raw19755step0Labels = mixedMoment B raw19755step1 raw19755step1Labels := by
      have ha : raw19755step1 = (fun i j => raw19755step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19755step1 raw19755step0; decide +kernel
      have hl : raw19755step1Labels = raw19755step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19755step0 raw19755step0Labels permutation137 permutation6
    mixedMoment B raw19755step1 raw19755step1Labels = mixedMoment B raw19755step2 raw19755step2Labels := by
      have ha : raw19755step2 = -raw19755step1 := by apply Matrix.ext; change ∀ i j, raw19755step2 i j = -(raw19755step1 i j); unfold raw19755step2 raw19755step1; decide +kernel
      have hl : raw19755step2Labels = raw19755step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19755step2 raw19755step2Labels = mixedMoment B raw19755step3 raw19755step3Labels := by
      have ha : raw19755step3 = raw19755step2 := by apply Matrix.ext; unfold raw19755step3 raw19755step2; decide +kernel
      have hl : raw19755step2Labels = labelEmbedding9 ∘ raw19755step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19755step2 raw19755step2Labels raw19755step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4394 node4394Labels := by rfl

def raw19756 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19756step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19756step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19756 raw19756Labels = mixedMoment B node4394 node4394Labels := by
  calc
    mixedMoment B raw19756 raw19756Labels = mixedMoment B raw19756step0 raw19756step0Labels := by
      have hz : ∀ j, raw19756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19756step0 = (fun i j => raw19756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19756step0 raw19756; decide +kernel
      have hl : raw19756step0Labels = raw19756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19756 raw19756Labels permutation346 hz
    mixedMoment B raw19756step0 raw19756step0Labels = mixedMoment B raw19756step1 raw19756step1Labels := by
      have ha : raw19756step1 = (fun i j => raw19756step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19756step1 raw19756step0; decide +kernel
      have hl : raw19756step1Labels = raw19756step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19756step0 raw19756step0Labels permutation137 permutation6
    mixedMoment B raw19756step1 raw19756step1Labels = mixedMoment B raw19756step2 raw19756step2Labels := by
      have ha : raw19756step2 = -raw19756step1 := by apply Matrix.ext; change ∀ i j, raw19756step2 i j = -(raw19756step1 i j); unfold raw19756step2 raw19756step1; decide +kernel
      have hl : raw19756step2Labels = raw19756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19756step2 raw19756step2Labels = mixedMoment B raw19756step3 raw19756step3Labels := by
      have ha : raw19756step3 = raw19756step2 := by apply Matrix.ext; unfold raw19756step3 raw19756step2; decide +kernel
      have hl : raw19756step2Labels = labelEmbedding9 ∘ raw19756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19756step2 raw19756step2Labels raw19756step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4394 node4394Labels := by rfl

def raw19757 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw19757step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19757step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw19757step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19757step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw19757step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19757 raw19757Labels = mixedMoment B node4413 node4413Labels := by
  calc
    mixedMoment B raw19757 raw19757Labels = mixedMoment B raw19757step0 raw19757step0Labels := by
      have hz : ∀ j, raw19757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19757step0 = (fun i j => raw19757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19757step0 raw19757; decide +kernel
      have hl : raw19757step0Labels = raw19757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19757 raw19757Labels permutation434 hz
    mixedMoment B raw19757step0 raw19757step0Labels = mixedMoment B raw19757step1 raw19757step1Labels := by
      have hz : ∀ j, raw19757step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19757step1 = (fun i j => raw19757step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19757step1 raw19757step0; decide +kernel
      have hl : raw19757step1Labels = raw19757step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19757step0 raw19757step0Labels permutation80 hz
    mixedMoment B raw19757step1 raw19757step1Labels = mixedMoment B raw19757step2 raw19757step2Labels := by
      have ha : raw19757step2 = (fun i j => raw19757step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19757step2 raw19757step1; decide +kernel
      have hl : raw19757step2Labels = raw19757step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19757step1 raw19757step1Labels permutation29 permutation6
    mixedMoment B raw19757step2 raw19757step2Labels = mixedMoment B raw19757step3 raw19757step3Labels := by
      have ha : raw19757step3 = -raw19757step2 := by apply Matrix.ext; change ∀ i j, raw19757step3 i j = -(raw19757step2 i j); unfold raw19757step3 raw19757step2; decide +kernel
      have hl : raw19757step3Labels = raw19757step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19757step3 raw19757step3Labels = mixedMoment B raw19757step4 raw19757step4Labels := by
      have ha : raw19757step4 = raw19757step3 := by apply Matrix.ext; unfold raw19757step4 raw19757step3; decide +kernel
      have hl : raw19757step3Labels = labelEmbedding9 ∘ raw19757step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19757step3 raw19757step3Labels raw19757step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4413 node4413Labels := by rfl

def raw19758 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19758step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19758step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19758step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19758 raw19758Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19758 raw19758Labels = mixedMoment B raw19758step0 raw19758step0Labels := by
      have hz : ∀ j, raw19758 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19758step0 = (fun i j => raw19758 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19758step0 raw19758; decide +kernel
      have hl : raw19758step0Labels = raw19758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19758 raw19758Labels permutation434 hz
    mixedMoment B raw19758step0 raw19758step0Labels = mixedMoment B raw19758step1 raw19758step1Labels := by
      have hz : ∀ j, raw19758step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19758step1 = (fun i j => raw19758step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19758step1 raw19758step0; decide +kernel
      have hl : raw19758step1Labels = raw19758step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19758step0 raw19758step0Labels permutation56 hz
    mixedMoment B raw19758step1 raw19758step1Labels = mixedMoment B raw19758step2 raw19758step2Labels := by
      have ha : raw19758step2 = (fun i j => raw19758step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19758step2 raw19758step1; decide +kernel
      have hl : raw19758step2Labels = raw19758step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19758step1 raw19758step1Labels permutation10 permutation6
    mixedMoment B raw19758step2 raw19758step2Labels = mixedMoment B raw19758step3 raw19758step3Labels := by
      have ha : raw19758step3 = raw19758step2 := by apply Matrix.ext; unfold raw19758step3 raw19758step2; decide +kernel
      have hl : raw19758step2Labels = labelEmbedding9 ∘ raw19758step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19758step2 raw19758step2Labels raw19758step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19759 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19759step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19759step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19759step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19759step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19759 raw19759Labels = mixedMoment B node4394 node4394Labels := by
  calc
    mixedMoment B raw19759 raw19759Labels = mixedMoment B raw19759step0 raw19759step0Labels := by
      have hz : ∀ j, raw19759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19759step0 = (fun i j => raw19759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19759step0 raw19759; decide +kernel
      have hl : raw19759step0Labels = raw19759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19759 raw19759Labels permutation434 hz
    mixedMoment B raw19759step0 raw19759step0Labels = mixedMoment B raw19759step1 raw19759step1Labels := by
      have ha : raw19759step1 = (fun i j => raw19759step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19759step1 raw19759step0; decide +kernel
      have hl : raw19759step1Labels = raw19759step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19759step0 raw19759step0Labels permutation143 permutation6
    mixedMoment B raw19759step1 raw19759step1Labels = mixedMoment B raw19759step2 raw19759step2Labels := by
      have ha : raw19759step2 = -raw19759step1 := by apply Matrix.ext; change ∀ i j, raw19759step2 i j = -(raw19759step1 i j); unfold raw19759step2 raw19759step1; decide +kernel
      have hl : raw19759step2Labels = raw19759step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19759step2 raw19759step2Labels = mixedMoment B raw19759step3 raw19759step3Labels := by
      have ha : raw19759step3 = raw19759step2 := by apply Matrix.ext; unfold raw19759step3 raw19759step2; decide +kernel
      have hl : raw19759step2Labels = labelEmbedding9 ∘ raw19759step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19759step2 raw19759step2Labels raw19759step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4394 node4394Labels := by rfl

def raw19760 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19760step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19760step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19760step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19760step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19760 raw19760Labels = mixedMoment B node4394 node4394Labels := by
  calc
    mixedMoment B raw19760 raw19760Labels = mixedMoment B raw19760step0 raw19760step0Labels := by
      have hz : ∀ j, raw19760 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19760step0 = (fun i j => raw19760 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19760step0 raw19760; decide +kernel
      have hl : raw19760step0Labels = raw19760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19760 raw19760Labels permutation265 hz
    mixedMoment B raw19760step0 raw19760step0Labels = mixedMoment B raw19760step1 raw19760step1Labels := by
      have ha : raw19760step1 = (fun i j => raw19760step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19760step1 raw19760step0; decide +kernel
      have hl : raw19760step1Labels = raw19760step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19760step0 raw19760step0Labels permutation137 permutation6
    mixedMoment B raw19760step1 raw19760step1Labels = mixedMoment B raw19760step2 raw19760step2Labels := by
      have ha : raw19760step2 = -raw19760step1 := by apply Matrix.ext; change ∀ i j, raw19760step2 i j = -(raw19760step1 i j); unfold raw19760step2 raw19760step1; decide +kernel
      have hl : raw19760step2Labels = raw19760step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19760step2 raw19760step2Labels = mixedMoment B raw19760step3 raw19760step3Labels := by
      have ha : raw19760step3 = raw19760step2 := by apply Matrix.ext; unfold raw19760step3 raw19760step2; decide +kernel
      have hl : raw19760step2Labels = labelEmbedding9 ∘ raw19760step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19760step2 raw19760step2Labels raw19760step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4394 node4394Labels := by rfl

def raw19761 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw19761step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw19761step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19761step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw19761step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19761 raw19761Labels = mixedMoment B node4413 node4413Labels := by
  calc
    mixedMoment B raw19761 raw19761Labels = mixedMoment B raw19761step0 raw19761step0Labels := by
      have hz : ∀ j, raw19761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19761step0 = (fun i j => raw19761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19761step0 raw19761; decide +kernel
      have hl : raw19761step0Labels = raw19761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19761 raw19761Labels permutation434 hz
    mixedMoment B raw19761step0 raw19761step0Labels = mixedMoment B raw19761step1 raw19761step1Labels := by
      have hz : ∀ j, raw19761step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19761step1 = (fun i j => raw19761step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19761step1 raw19761step0; decide +kernel
      have hl : raw19761step1Labels = raw19761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19761step0 raw19761step0Labels permutation56 hz
    mixedMoment B raw19761step1 raw19761step1Labels = mixedMoment B raw19761step2 raw19761step2Labels := by
      have ha : raw19761step2 = (fun i j => raw19761step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19761step2 raw19761step1; decide +kernel
      have hl : raw19761step2Labels = raw19761step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19761step1 raw19761step1Labels permutation29 permutation6
    mixedMoment B raw19761step2 raw19761step2Labels = mixedMoment B raw19761step3 raw19761step3Labels := by
      have ha : raw19761step3 = -raw19761step2 := by apply Matrix.ext; change ∀ i j, raw19761step3 i j = -(raw19761step2 i j); unfold raw19761step3 raw19761step2; decide +kernel
      have hl : raw19761step3Labels = raw19761step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19761step3 raw19761step3Labels = mixedMoment B raw19761step4 raw19761step4Labels := by
      have ha : raw19761step4 = raw19761step3 := by apply Matrix.ext; unfold raw19761step4 raw19761step3; decide +kernel
      have hl : raw19761step3Labels = labelEmbedding9 ∘ raw19761step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19761step3 raw19761step3Labels raw19761step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4413 node4413Labels := by rfl

def raw19762 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19762step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19762step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19762step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19762 raw19762Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19762 raw19762Labels = mixedMoment B raw19762step0 raw19762step0Labels := by
      have hz : ∀ j, raw19762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19762step0 = (fun i j => raw19762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19762step0 raw19762; decide +kernel
      have hl : raw19762step0Labels = raw19762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19762 raw19762Labels permutation346 hz
    mixedMoment B raw19762step0 raw19762step0Labels = mixedMoment B raw19762step1 raw19762step1Labels := by
      have hz : ∀ j, raw19762step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19762step1 = (fun i j => raw19762step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19762step1 raw19762step0; decide +kernel
      have hl : raw19762step1Labels = raw19762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19762step0 raw19762step0Labels permutation56 hz
    mixedMoment B raw19762step1 raw19762step1Labels = mixedMoment B raw19762step2 raw19762step2Labels := by
      have ha : raw19762step2 = (fun i j => raw19762step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19762step2 raw19762step1; decide +kernel
      have hl : raw19762step2Labels = raw19762step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19762step1 raw19762step1Labels permutation10 permutation6
    mixedMoment B raw19762step2 raw19762step2Labels = mixedMoment B raw19762step3 raw19762step3Labels := by
      have ha : raw19762step3 = raw19762step2 := by apply Matrix.ext; unfold raw19762step3 raw19762step2; decide +kernel
      have hl : raw19762step2Labels = labelEmbedding9 ∘ raw19762step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19762step2 raw19762step2Labels raw19762step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19763 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19763step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19763step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19763step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19763step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19763 raw19763Labels = mixedMoment B node4394 node4394Labels := by
  calc
    mixedMoment B raw19763 raw19763Labels = mixedMoment B raw19763step0 raw19763step0Labels := by
      have hz : ∀ j, raw19763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19763step0 = (fun i j => raw19763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19763step0 raw19763; decide +kernel
      have hl : raw19763step0Labels = raw19763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19763 raw19763Labels permutation346 hz
    mixedMoment B raw19763step0 raw19763step0Labels = mixedMoment B raw19763step1 raw19763step1Labels := by
      have ha : raw19763step1 = (fun i j => raw19763step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19763step1 raw19763step0; decide +kernel
      have hl : raw19763step1Labels = raw19763step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19763step0 raw19763step0Labels permutation143 permutation6
    mixedMoment B raw19763step1 raw19763step1Labels = mixedMoment B raw19763step2 raw19763step2Labels := by
      have ha : raw19763step2 = -raw19763step1 := by apply Matrix.ext; change ∀ i j, raw19763step2 i j = -(raw19763step1 i j); unfold raw19763step2 raw19763step1; decide +kernel
      have hl : raw19763step2Labels = raw19763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19763step2 raw19763step2Labels = mixedMoment B raw19763step3 raw19763step3Labels := by
      have ha : raw19763step3 = raw19763step2 := by apply Matrix.ext; unfold raw19763step3 raw19763step2; decide +kernel
      have hl : raw19763step2Labels = labelEmbedding9 ∘ raw19763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19763step2 raw19763step2Labels raw19763step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4394 node4394Labels := by rfl

def raw19764 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19764step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19764step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19764step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19764step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19764 raw19764Labels = mixedMoment B node4394 node4394Labels := by
  calc
    mixedMoment B raw19764 raw19764Labels = mixedMoment B raw19764step0 raw19764step0Labels := by
      have hz : ∀ j, raw19764 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19764step0 = (fun i j => raw19764 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19764step0 raw19764; decide +kernel
      have hl : raw19764step0Labels = raw19764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19764 raw19764Labels permutation265 hz
    mixedMoment B raw19764step0 raw19764step0Labels = mixedMoment B raw19764step1 raw19764step1Labels := by
      have ha : raw19764step1 = (fun i j => raw19764step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19764step1 raw19764step0; decide +kernel
      have hl : raw19764step1Labels = raw19764step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19764step0 raw19764step0Labels permutation143 permutation6
    mixedMoment B raw19764step1 raw19764step1Labels = mixedMoment B raw19764step2 raw19764step2Labels := by
      have ha : raw19764step2 = -raw19764step1 := by apply Matrix.ext; change ∀ i j, raw19764step2 i j = -(raw19764step1 i j); unfold raw19764step2 raw19764step1; decide +kernel
      have hl : raw19764step2Labels = raw19764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19764step2 raw19764step2Labels = mixedMoment B raw19764step3 raw19764step3Labels := by
      have ha : raw19764step3 = raw19764step2 := by apply Matrix.ext; unfold raw19764step3 raw19764step2; decide +kernel
      have hl : raw19764step2Labels = labelEmbedding9 ∘ raw19764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19764step2 raw19764step2Labels raw19764step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4394 node4394Labels := by rfl

def raw19765 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw19765step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw19765step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19765step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw19765step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19765 raw19765Labels = mixedMoment B node4413 node4413Labels := by
  calc
    mixedMoment B raw19765 raw19765Labels = mixedMoment B raw19765step0 raw19765step0Labels := by
      have hz : ∀ j, raw19765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19765step0 = (fun i j => raw19765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19765step0 raw19765; decide +kernel
      have hl : raw19765step0Labels = raw19765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19765 raw19765Labels permutation346 hz
    mixedMoment B raw19765step0 raw19765step0Labels = mixedMoment B raw19765step1 raw19765step1Labels := by
      have hz : ∀ j, raw19765step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19765step1 = (fun i j => raw19765step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19765step1 raw19765step0; decide +kernel
      have hl : raw19765step1Labels = raw19765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19765step0 raw19765step0Labels permutation56 hz
    mixedMoment B raw19765step1 raw19765step1Labels = mixedMoment B raw19765step2 raw19765step2Labels := by
      have ha : raw19765step2 = (fun i j => raw19765step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19765step2 raw19765step1; decide +kernel
      have hl : raw19765step2Labels = raw19765step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19765step1 raw19765step1Labels permutation29 permutation6
    mixedMoment B raw19765step2 raw19765step2Labels = mixedMoment B raw19765step3 raw19765step3Labels := by
      have ha : raw19765step3 = -raw19765step2 := by apply Matrix.ext; change ∀ i j, raw19765step3 i j = -(raw19765step2 i j); unfold raw19765step3 raw19765step2; decide +kernel
      have hl : raw19765step3Labels = raw19765step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19765step3 raw19765step3Labels = mixedMoment B raw19765step4 raw19765step4Labels := by
      have ha : raw19765step4 = raw19765step3 := by apply Matrix.ext; unfold raw19765step4 raw19765step3; decide +kernel
      have hl : raw19765step3Labels = labelEmbedding9 ∘ raw19765step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19765step3 raw19765step3Labels raw19765step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4413 node4413Labels := by rfl

def raw19766 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19766step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, -2, 4]]
def raw19766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19766step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 2, -4], ![-2, -2, 4]]
def raw19766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19766step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw19766step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19766step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw19766step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19766 raw19766Labels = mixedMoment B node4629 node4629Labels := by
  calc
    mixedMoment B raw19766 raw19766Labels = mixedMoment B raw19766step0 raw19766step0Labels := by
      have hz : ∀ j, raw19766 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19766step0 = (fun i j => raw19766 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19766step0 raw19766; decide +kernel
      have hl : raw19766step0Labels = raw19766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19766 raw19766Labels permutation520 hz
    mixedMoment B raw19766step0 raw19766step0Labels = mixedMoment B raw19766step1 raw19766step1Labels := by
      have hz : ∀ j, raw19766step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19766step1 = (fun i j => raw19766step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19766step1 raw19766step0; decide +kernel
      have hl : raw19766step1Labels = raw19766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19766step0 raw19766step0Labels permutation104 hz
    mixedMoment B raw19766step1 raw19766step1Labels = mixedMoment B raw19766step2 raw19766step2Labels := by
      have hz : ∀ j, raw19766step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19766step2 = (fun i j => raw19766step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19766step2 raw19766step1; decide +kernel
      have hl : raw19766step2Labels = raw19766step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19766step1 raw19766step1Labels permutation20 hz
    mixedMoment B raw19766step2 raw19766step2Labels = mixedMoment B raw19766step3 raw19766step3Labels := by
      have hz : ∀ j, raw19766step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19766step3 = (fun i j => raw19766step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19766step3 raw19766step2; decide +kernel
      have hl : raw19766step3Labels = raw19766step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19766step2 raw19766step2Labels permutation4 hz
    mixedMoment B raw19766step3 raw19766step3Labels = mixedMoment B raw19766step4 raw19766step4Labels := by
      have ha : raw19766step4 = (fun i j => raw19766step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19766step4 raw19766step3; decide +kernel
      have hl : raw19766step4Labels = raw19766step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19766step3 raw19766step3Labels permutation0 permutation6
    mixedMoment B raw19766step4 raw19766step4Labels = mixedMoment B raw19766step5 raw19766step5Labels := by
      have ha : raw19766step5 = raw19766step4 := by apply Matrix.ext; unfold raw19766step5 raw19766step4; decide +kernel
      have hl : raw19766step4Labels = labelEmbedding9 ∘ raw19766step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19766step4 raw19766step4Labels raw19766step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4629 node4629Labels := by rfl

def raw19767 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19767step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19767step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-4, 1, 3]]
def raw19767step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19767step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19767step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19767step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19767step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19767 raw19767Labels = mixedMoment B node4274 node4274Labels := by
  calc
    mixedMoment B raw19767 raw19767Labels = mixedMoment B raw19767step0 raw19767step0Labels := by
      have hz : ∀ j, raw19767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19767step0 = (fun i j => raw19767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19767step0 raw19767; decide +kernel
      have hl : raw19767step0Labels = raw19767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19767 raw19767Labels permutation434 hz
    mixedMoment B raw19767step0 raw19767step0Labels = mixedMoment B raw19767step1 raw19767step1Labels := by
      have hz : ∀ j, raw19767step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19767step1 = (fun i j => raw19767step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19767step1 raw19767step0; decide +kernel
      have hl : raw19767step1Labels = raw19767step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19767step0 raw19767step0Labels permutation80 hz
    mixedMoment B raw19767step1 raw19767step1Labels = mixedMoment B raw19767step2 raw19767step2Labels := by
      have hz : ∀ j, raw19767step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19767step2 = (fun i j => raw19767step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19767step2 raw19767step1; decide +kernel
      have hl : raw19767step2Labels = raw19767step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19767step1 raw19767step1Labels permutation14 hz
    mixedMoment B raw19767step2 raw19767step2Labels = mixedMoment B raw19767step3 raw19767step3Labels := by
      have ha : raw19767step3 = (fun i j => raw19767step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19767step3 raw19767step2; decide +kernel
      have hl : raw19767step3Labels = raw19767step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19767step2 raw19767step2Labels permutation7 permutation6
    mixedMoment B raw19767step3 raw19767step3Labels = mixedMoment B raw19767step4 raw19767step4Labels := by
      have ha : raw19767step4 = -raw19767step3 := by apply Matrix.ext; change ∀ i j, raw19767step4 i j = -(raw19767step3 i j); unfold raw19767step4 raw19767step3; decide +kernel
      have hl : raw19767step4Labels = raw19767step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19767step4 raw19767step4Labels = mixedMoment B raw19767step5 raw19767step5Labels := by
      have ha : raw19767step5 = raw19767step4 := by apply Matrix.ext; unfold raw19767step5 raw19767step4; decide +kernel
      have hl : raw19767step4Labels = labelEmbedding9 ∘ raw19767step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19767step4 raw19767step4Labels raw19767step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4274 node4274Labels := by rfl

def raw19768 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19768step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19768step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19768step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19768step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19768step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19768 raw19768Labels = mixedMoment B node4257 node4257Labels := by
  calc
    mixedMoment B raw19768 raw19768Labels = mixedMoment B raw19768step0 raw19768step0Labels := by
      have hz : ∀ j, raw19768 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19768step0 = (fun i j => raw19768 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19768step0 raw19768; decide +kernel
      have hl : raw19768step0Labels = raw19768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19768 raw19768Labels permutation434 hz
    mixedMoment B raw19768step0 raw19768step0Labels = mixedMoment B raw19768step1 raw19768step1Labels := by
      have hz : ∀ j, raw19768step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19768step1 = (fun i j => raw19768step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19768step1 raw19768step0; decide +kernel
      have hl : raw19768step1Labels = raw19768step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19768step0 raw19768step0Labels permutation80 hz
    mixedMoment B raw19768step1 raw19768step1Labels = mixedMoment B raw19768step2 raw19768step2Labels := by
      have ha : raw19768step2 = (fun i j => raw19768step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19768step2 raw19768step1; decide +kernel
      have hl : raw19768step2Labels = raw19768step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19768step1 raw19768step1Labels permutation29 permutation6
    mixedMoment B raw19768step2 raw19768step2Labels = mixedMoment B raw19768step3 raw19768step3Labels := by
      have ha : raw19768step3 = -raw19768step2 := by apply Matrix.ext; change ∀ i j, raw19768step3 i j = -(raw19768step2 i j); unfold raw19768step3 raw19768step2; decide +kernel
      have hl : raw19768step3Labels = raw19768step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19768step3 raw19768step3Labels = mixedMoment B raw19768step4 raw19768step4Labels := by
      have ha : raw19768step4 = raw19768step3 := by apply Matrix.ext; unfold raw19768step4 raw19768step3; decide +kernel
      have hl : raw19768step3Labels = labelEmbedding9 ∘ raw19768step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19768step3 raw19768step3Labels raw19768step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4257 node4257Labels := by rfl

def raw19769 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19769step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19769step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19769step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19769step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19769step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19769 raw19769Labels = mixedMoment B node4257 node4257Labels := by
  calc
    mixedMoment B raw19769 raw19769Labels = mixedMoment B raw19769step0 raw19769step0Labels := by
      have hz : ∀ j, raw19769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19769step0 = (fun i j => raw19769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19769step0 raw19769; decide +kernel
      have hl : raw19769step0Labels = raw19769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19769 raw19769Labels permutation434 hz
    mixedMoment B raw19769step0 raw19769step0Labels = mixedMoment B raw19769step1 raw19769step1Labels := by
      have hz : ∀ j, raw19769step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19769step1 = (fun i j => raw19769step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19769step1 raw19769step0; decide +kernel
      have hl : raw19769step1Labels = raw19769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19769step0 raw19769step0Labels permutation56 hz
    mixedMoment B raw19769step1 raw19769step1Labels = mixedMoment B raw19769step2 raw19769step2Labels := by
      have ha : raw19769step2 = (fun i j => raw19769step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19769step2 raw19769step1; decide +kernel
      have hl : raw19769step2Labels = raw19769step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19769step1 raw19769step1Labels permutation29 permutation6
    mixedMoment B raw19769step2 raw19769step2Labels = mixedMoment B raw19769step3 raw19769step3Labels := by
      have ha : raw19769step3 = -raw19769step2 := by apply Matrix.ext; change ∀ i j, raw19769step3 i j = -(raw19769step2 i j); unfold raw19769step3 raw19769step2; decide +kernel
      have hl : raw19769step3Labels = raw19769step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19769step3 raw19769step3Labels = mixedMoment B raw19769step4 raw19769step4Labels := by
      have ha : raw19769step4 = raw19769step3 := by apply Matrix.ext; unfold raw19769step4 raw19769step3; decide +kernel
      have hl : raw19769step3Labels = labelEmbedding9 ∘ raw19769step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19769step3 raw19769step3Labels raw19769step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4257 node4257Labels := by rfl

def raw19770 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19770step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19770step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19770step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19770step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19770step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19770step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19770 raw19770Labels = mixedMoment B node4257 node4257Labels := by
  calc
    mixedMoment B raw19770 raw19770Labels = mixedMoment B raw19770step0 raw19770step0Labels := by
      have hz : ∀ j, raw19770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19770step0 = (fun i j => raw19770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19770step0 raw19770; decide +kernel
      have hl : raw19770step0Labels = raw19770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19770 raw19770Labels permutation346 hz
    mixedMoment B raw19770step0 raw19770step0Labels = mixedMoment B raw19770step1 raw19770step1Labels := by
      have hz : ∀ j, raw19770step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19770step1 = (fun i j => raw19770step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19770step1 raw19770step0; decide +kernel
      have hl : raw19770step1Labels = raw19770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19770step0 raw19770step0Labels permutation56 hz
    mixedMoment B raw19770step1 raw19770step1Labels = mixedMoment B raw19770step2 raw19770step2Labels := by
      have ha : raw19770step2 = (fun i j => raw19770step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19770step2 raw19770step1; decide +kernel
      have hl : raw19770step2Labels = raw19770step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19770step1 raw19770step1Labels permutation29 permutation6
    mixedMoment B raw19770step2 raw19770step2Labels = mixedMoment B raw19770step3 raw19770step3Labels := by
      have ha : raw19770step3 = -raw19770step2 := by apply Matrix.ext; change ∀ i j, raw19770step3 i j = -(raw19770step2 i j); unfold raw19770step3 raw19770step2; decide +kernel
      have hl : raw19770step3Labels = raw19770step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19770step3 raw19770step3Labels = mixedMoment B raw19770step4 raw19770step4Labels := by
      have ha : raw19770step4 = raw19770step3 := by apply Matrix.ext; unfold raw19770step4 raw19770step3; decide +kernel
      have hl : raw19770step3Labels = labelEmbedding9 ∘ raw19770step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19770step3 raw19770step3Labels raw19770step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4257 node4257Labels := by rfl

def raw19771 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19771step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -4, 4]]
def raw19771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19771step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-4, 2, 2]]
def raw19771step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19771step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw19771step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19771step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw19771step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19771 raw19771Labels = mixedMoment B node4280 node4280Labels := by
  calc
    mixedMoment B raw19771 raw19771Labels = mixedMoment B raw19771step0 raw19771step0Labels := by
      have hz : ∀ j, raw19771 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19771step0 = (fun i j => raw19771 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19771step0 raw19771; decide +kernel
      have hl : raw19771step0Labels = raw19771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19771 raw19771Labels permutation434 hz
    mixedMoment B raw19771step0 raw19771step0Labels = mixedMoment B raw19771step1 raw19771step1Labels := by
      have hz : ∀ j, raw19771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19771step1 = (fun i j => raw19771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19771step1 raw19771step0; decide +kernel
      have hl : raw19771step1Labels = raw19771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19771step0 raw19771step0Labels permutation80 hz
    mixedMoment B raw19771step1 raw19771step1Labels = mixedMoment B raw19771step2 raw19771step2Labels := by
      have hz : ∀ j, raw19771step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19771step2 = (fun i j => raw19771step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19771step2 raw19771step1; decide +kernel
      have hl : raw19771step2Labels = raw19771step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19771step1 raw19771step1Labels permutation14 hz
    mixedMoment B raw19771step2 raw19771step2Labels = mixedMoment B raw19771step3 raw19771step3Labels := by
      have ha : raw19771step3 = (fun i j => raw19771step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19771step3 raw19771step2; decide +kernel
      have hl : raw19771step3Labels = raw19771step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19771step2 raw19771step2Labels permutation7 permutation6
    mixedMoment B raw19771step3 raw19771step3Labels = mixedMoment B raw19771step4 raw19771step4Labels := by
      have ha : raw19771step4 = -raw19771step3 := by apply Matrix.ext; change ∀ i j, raw19771step4 i j = -(raw19771step3 i j); unfold raw19771step4 raw19771step3; decide +kernel
      have hl : raw19771step4Labels = raw19771step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19771step4 raw19771step4Labels = mixedMoment B raw19771step5 raw19771step5Labels := by
      have ha : raw19771step5 = raw19771step4 := by apply Matrix.ext; unfold raw19771step5 raw19771step4; decide +kernel
      have hl : raw19771step4Labels = labelEmbedding9 ∘ raw19771step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19771step4 raw19771step4Labels raw19771step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4280 node4280Labels := by rfl

def raw19772 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19772step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19772step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19772step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw19772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19772step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19772step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19772 raw19772Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw19772 raw19772Labels = mixedMoment B raw19772step0 raw19772step0Labels := by
      have hz : ∀ j, raw19772 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19772step0 = (fun i j => raw19772 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19772step0 raw19772; decide +kernel
      have hl : raw19772step0Labels = raw19772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19772 raw19772Labels permutation434 hz
    mixedMoment B raw19772step0 raw19772step0Labels = mixedMoment B raw19772step1 raw19772step1Labels := by
      have hz : ∀ j, raw19772step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19772step1 = (fun i j => raw19772step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19772step1 raw19772step0; decide +kernel
      have hl : raw19772step1Labels = raw19772step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19772step0 raw19772step0Labels permutation80 hz
    mixedMoment B raw19772step1 raw19772step1Labels = mixedMoment B raw19772step2 raw19772step2Labels := by
      have ha : raw19772step2 = (fun i j => raw19772step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19772step2 raw19772step1; decide +kernel
      have hl : raw19772step2Labels = raw19772step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19772step1 raw19772step1Labels permutation29 permutation6
    mixedMoment B raw19772step2 raw19772step2Labels = mixedMoment B raw19772step3 raw19772step3Labels := by
      have ha : raw19772step3 = -raw19772step2 := by apply Matrix.ext; change ∀ i j, raw19772step3 i j = -(raw19772step2 i j); unfold raw19772step3 raw19772step2; decide +kernel
      have hl : raw19772step3Labels = raw19772step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1027 node1027Labels := by rfl

def raw19773 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19773step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19773step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw19773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19773step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19773step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19773 raw19773Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw19773 raw19773Labels = mixedMoment B raw19773step0 raw19773step0Labels := by
      have hz : ∀ j, raw19773 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19773step0 = (fun i j => raw19773 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19773step0 raw19773; decide +kernel
      have hl : raw19773step0Labels = raw19773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19773 raw19773Labels permutation434 hz
    mixedMoment B raw19773step0 raw19773step0Labels = mixedMoment B raw19773step1 raw19773step1Labels := by
      have hz : ∀ j, raw19773step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19773step1 = (fun i j => raw19773step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19773step1 raw19773step0; decide +kernel
      have hl : raw19773step1Labels = raw19773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19773step0 raw19773step0Labels permutation56 hz
    mixedMoment B raw19773step1 raw19773step1Labels = mixedMoment B raw19773step2 raw19773step2Labels := by
      have ha : raw19773step2 = (fun i j => raw19773step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19773step2 raw19773step1; decide +kernel
      have hl : raw19773step2Labels = raw19773step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19773step1 raw19773step1Labels permutation29 permutation6
    mixedMoment B raw19773step2 raw19773step2Labels = mixedMoment B raw19773step3 raw19773step3Labels := by
      have ha : raw19773step3 = -raw19773step2 := by apply Matrix.ext; change ∀ i j, raw19773step3 i j = -(raw19773step2 i j); unfold raw19773step3 raw19773step2; decide +kernel
      have hl : raw19773step3Labels = raw19773step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1027 node1027Labels := by rfl

def raw19774 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19774step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19774step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw19774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19774step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19774step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19774 raw19774Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw19774 raw19774Labels = mixedMoment B raw19774step0 raw19774step0Labels := by
      have hz : ∀ j, raw19774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19774step0 = (fun i j => raw19774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19774step0 raw19774; decide +kernel
      have hl : raw19774step0Labels = raw19774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19774 raw19774Labels permutation346 hz
    mixedMoment B raw19774step0 raw19774step0Labels = mixedMoment B raw19774step1 raw19774step1Labels := by
      have hz : ∀ j, raw19774step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19774step1 = (fun i j => raw19774step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19774step1 raw19774step0; decide +kernel
      have hl : raw19774step1Labels = raw19774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19774step0 raw19774step0Labels permutation56 hz
    mixedMoment B raw19774step1 raw19774step1Labels = mixedMoment B raw19774step2 raw19774step2Labels := by
      have ha : raw19774step2 = (fun i j => raw19774step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19774step2 raw19774step1; decide +kernel
      have hl : raw19774step2Labels = raw19774step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19774step1 raw19774step1Labels permutation29 permutation6
    mixedMoment B raw19774step2 raw19774step2Labels = mixedMoment B raw19774step3 raw19774step3Labels := by
      have ha : raw19774step3 = -raw19774step2 := by apply Matrix.ext; change ∀ i j, raw19774step3 i j = -(raw19774step2 i j); unfold raw19774step3 raw19774step2; decide +kernel
      have hl : raw19774step3Labels = raw19774step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1027 node1027Labels := by rfl

def raw19775 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19775step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19775step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19775step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, -3, 4]]
def raw19775step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19775step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-4, 3, 1]]
def raw19775step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19775step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw19775step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19775 raw19775Labels = mixedMoment B node1064 node1064Labels := by
  calc
    mixedMoment B raw19775 raw19775Labels = mixedMoment B raw19775step0 raw19775step0Labels := by
      have hz : ∀ j, raw19775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19775step0 = (fun i j => raw19775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19775step0 raw19775; decide +kernel
      have hl : raw19775step0Labels = raw19775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19775 raw19775Labels permutation434 hz
    mixedMoment B raw19775step0 raw19775step0Labels = mixedMoment B raw19775step1 raw19775step1Labels := by
      have hz : ∀ j, raw19775step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19775step1 = (fun i j => raw19775step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19775step1 raw19775step0; decide +kernel
      have hl : raw19775step1Labels = raw19775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19775step0 raw19775step0Labels permutation80 hz
    mixedMoment B raw19775step1 raw19775step1Labels = mixedMoment B raw19775step2 raw19775step2Labels := by
      have hz : ∀ j, raw19775step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19775step2 = (fun i j => raw19775step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19775step2 raw19775step1; decide +kernel
      have hl : raw19775step2Labels = raw19775step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19775step1 raw19775step1Labels permutation14 hz
    mixedMoment B raw19775step2 raw19775step2Labels = mixedMoment B raw19775step3 raw19775step3Labels := by
      have ha : raw19775step3 = (fun i j => raw19775step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19775step3 raw19775step2; decide +kernel
      have hl : raw19775step3Labels = raw19775step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19775step2 raw19775step2Labels permutation7 permutation6
    mixedMoment B raw19775step3 raw19775step3Labels = mixedMoment B raw19775step4 raw19775step4Labels := by
      have ha : raw19775step4 = -raw19775step3 := by apply Matrix.ext; change ∀ i j, raw19775step4 i j = -(raw19775step3 i j); unfold raw19775step4 raw19775step3; decide +kernel
      have hl : raw19775step4Labels = raw19775step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1064 node1064Labels := by rfl

def raw19776 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19776step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19776step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19776 raw19776Labels = mixedMoment B node986 node986Labels := by
  calc
    mixedMoment B raw19776 raw19776Labels = mixedMoment B raw19776step0 raw19776step0Labels := by
      have hz : ∀ j, raw19776 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19776step0 = (fun i j => raw19776 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19776step0 raw19776; decide +kernel
      have hl : raw19776step0Labels = raw19776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19776 raw19776Labels permutation434 hz
    mixedMoment B raw19776step0 raw19776step0Labels = mixedMoment B raw19776step1 raw19776step1Labels := by
      have hz : ∀ j, raw19776step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19776step1 = (fun i j => raw19776step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19776step1 raw19776step0; decide +kernel
      have hl : raw19776step1Labels = raw19776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19776step0 raw19776step0Labels permutation80 hz
    mixedMoment B raw19776step1 raw19776step1Labels = mixedMoment B raw19776step2 raw19776step2Labels := by
      have ha : raw19776step2 = (fun i j => raw19776step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19776step2 raw19776step1; decide +kernel
      have hl : raw19776step2Labels = raw19776step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19776step1 raw19776step1Labels permutation10 permutation6
    _ = mixedMoment B node986 node986Labels := by rfl

def raw19777 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19777 raw19777Labels = mixedMoment B node975 node975Labels := by
  calc
    mixedMoment B raw19777 raw19777Labels = mixedMoment B raw19777step0 raw19777step0Labels := by
      have hz : ∀ j, raw19777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19777step0 = (fun i j => raw19777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19777step0 raw19777; decide +kernel
      have hl : raw19777step0Labels = raw19777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19777 raw19777Labels permutation434 hz
    mixedMoment B raw19777step0 raw19777step0Labels = mixedMoment B raw19777step1 raw19777step1Labels := by
      have ha : raw19777step1 = (fun i j => raw19777step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19777step1 raw19777step0; decide +kernel
      have hl : raw19777step1Labels = raw19777step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19777step0 raw19777step0Labels permutation137 permutation6
    mixedMoment B raw19777step1 raw19777step1Labels = mixedMoment B raw19777step2 raw19777step2Labels := by
      have ha : raw19777step2 = -raw19777step1 := by apply Matrix.ext; change ∀ i j, raw19777step2 i j = -(raw19777step1 i j); unfold raw19777step2 raw19777step1; decide +kernel
      have hl : raw19777step2Labels = raw19777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node975 node975Labels := by rfl

def raw19778 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19778 raw19778Labels = mixedMoment B node975 node975Labels := by
  calc
    mixedMoment B raw19778 raw19778Labels = mixedMoment B raw19778step0 raw19778step0Labels := by
      have hz : ∀ j, raw19778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19778step0 = (fun i j => raw19778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19778step0 raw19778; decide +kernel
      have hl : raw19778step0Labels = raw19778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19778 raw19778Labels permutation346 hz
    mixedMoment B raw19778step0 raw19778step0Labels = mixedMoment B raw19778step1 raw19778step1Labels := by
      have ha : raw19778step1 = (fun i j => raw19778step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19778step1 raw19778step0; decide +kernel
      have hl : raw19778step1Labels = raw19778step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19778step0 raw19778step0Labels permutation137 permutation6
    mixedMoment B raw19778step1 raw19778step1Labels = mixedMoment B raw19778step2 raw19778step2Labels := by
      have ha : raw19778step2 = -raw19778step1 := by apply Matrix.ext; change ∀ i j, raw19778step2 i j = -(raw19778step1 i j); unfold raw19778step2 raw19778step1; decide +kernel
      have hl : raw19778step2Labels = raw19778step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node975 node975Labels := by rfl

def raw19779 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19779step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw19779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19779step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw19779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19779 raw19779Labels = mixedMoment B node994 node994Labels := by
  calc
    mixedMoment B raw19779 raw19779Labels = mixedMoment B raw19779step0 raw19779step0Labels := by
      have hz : ∀ j, raw19779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19779step0 = (fun i j => raw19779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19779step0 raw19779; decide +kernel
      have hl : raw19779step0Labels = raw19779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19779 raw19779Labels permutation434 hz
    mixedMoment B raw19779step0 raw19779step0Labels = mixedMoment B raw19779step1 raw19779step1Labels := by
      have hz : ∀ j, raw19779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19779step1 = (fun i j => raw19779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19779step1 raw19779step0; decide +kernel
      have hl : raw19779step1Labels = raw19779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19779step0 raw19779step0Labels permutation80 hz
    mixedMoment B raw19779step1 raw19779step1Labels = mixedMoment B raw19779step2 raw19779step2Labels := by
      have ha : raw19779step2 = (fun i j => raw19779step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19779step2 raw19779step1; decide +kernel
      have hl : raw19779step2Labels = raw19779step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19779step1 raw19779step1Labels permutation29 permutation6
    mixedMoment B raw19779step2 raw19779step2Labels = mixedMoment B raw19779step3 raw19779step3Labels := by
      have ha : raw19779step3 = -raw19779step2 := by apply Matrix.ext; change ∀ i j, raw19779step3 i j = -(raw19779step2 i j); unfold raw19779step3 raw19779step2; decide +kernel
      have hl : raw19779step3Labels = raw19779step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node994 node994Labels := by rfl

def raw19780 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19780step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19780step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19780 raw19780Labels = mixedMoment B node986 node986Labels := by
  calc
    mixedMoment B raw19780 raw19780Labels = mixedMoment B raw19780step0 raw19780step0Labels := by
      have hz : ∀ j, raw19780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19780step0 = (fun i j => raw19780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19780step0 raw19780; decide +kernel
      have hl : raw19780step0Labels = raw19780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19780 raw19780Labels permutation434 hz
    mixedMoment B raw19780step0 raw19780step0Labels = mixedMoment B raw19780step1 raw19780step1Labels := by
      have hz : ∀ j, raw19780step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19780step1 = (fun i j => raw19780step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19780step1 raw19780step0; decide +kernel
      have hl : raw19780step1Labels = raw19780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19780step0 raw19780step0Labels permutation56 hz
    mixedMoment B raw19780step1 raw19780step1Labels = mixedMoment B raw19780step2 raw19780step2Labels := by
      have ha : raw19780step2 = (fun i j => raw19780step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19780step2 raw19780step1; decide +kernel
      have hl : raw19780step2Labels = raw19780step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19780step1 raw19780step1Labels permutation10 permutation6
    _ = mixedMoment B node986 node986Labels := by rfl

def raw19781 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19781 raw19781Labels = mixedMoment B node975 node975Labels := by
  calc
    mixedMoment B raw19781 raw19781Labels = mixedMoment B raw19781step0 raw19781step0Labels := by
      have hz : ∀ j, raw19781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19781step0 = (fun i j => raw19781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19781step0 raw19781; decide +kernel
      have hl : raw19781step0Labels = raw19781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19781 raw19781Labels permutation434 hz
    mixedMoment B raw19781step0 raw19781step0Labels = mixedMoment B raw19781step1 raw19781step1Labels := by
      have ha : raw19781step1 = (fun i j => raw19781step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19781step1 raw19781step0; decide +kernel
      have hl : raw19781step1Labels = raw19781step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19781step0 raw19781step0Labels permutation143 permutation6
    mixedMoment B raw19781step1 raw19781step1Labels = mixedMoment B raw19781step2 raw19781step2Labels := by
      have ha : raw19781step2 = -raw19781step1 := by apply Matrix.ext; change ∀ i j, raw19781step2 i j = -(raw19781step1 i j); unfold raw19781step2 raw19781step1; decide +kernel
      have hl : raw19781step2Labels = raw19781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node975 node975Labels := by rfl

def raw19782 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19782 raw19782Labels = mixedMoment B node975 node975Labels := by
  calc
    mixedMoment B raw19782 raw19782Labels = mixedMoment B raw19782step0 raw19782step0Labels := by
      have hz : ∀ j, raw19782 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19782step0 = (fun i j => raw19782 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19782step0 raw19782; decide +kernel
      have hl : raw19782step0Labels = raw19782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19782 raw19782Labels permutation265 hz
    mixedMoment B raw19782step0 raw19782step0Labels = mixedMoment B raw19782step1 raw19782step1Labels := by
      have ha : raw19782step1 = (fun i j => raw19782step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19782step1 raw19782step0; decide +kernel
      have hl : raw19782step1Labels = raw19782step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19782step0 raw19782step0Labels permutation137 permutation6
    mixedMoment B raw19782step1 raw19782step1Labels = mixedMoment B raw19782step2 raw19782step2Labels := by
      have ha : raw19782step2 = -raw19782step1 := by apply Matrix.ext; change ∀ i j, raw19782step2 i j = -(raw19782step1 i j); unfold raw19782step2 raw19782step1; decide +kernel
      have hl : raw19782step2Labels = raw19782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node975 node975Labels := by rfl

def raw19783 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19783step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw19783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19783step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw19783step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19783 raw19783Labels = mixedMoment B node994 node994Labels := by
  calc
    mixedMoment B raw19783 raw19783Labels = mixedMoment B raw19783step0 raw19783step0Labels := by
      have hz : ∀ j, raw19783 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19783step0 = (fun i j => raw19783 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19783step0 raw19783; decide +kernel
      have hl : raw19783step0Labels = raw19783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19783 raw19783Labels permutation434 hz
    mixedMoment B raw19783step0 raw19783step0Labels = mixedMoment B raw19783step1 raw19783step1Labels := by
      have hz : ∀ j, raw19783step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19783step1 = (fun i j => raw19783step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19783step1 raw19783step0; decide +kernel
      have hl : raw19783step1Labels = raw19783step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19783step0 raw19783step0Labels permutation56 hz
    mixedMoment B raw19783step1 raw19783step1Labels = mixedMoment B raw19783step2 raw19783step2Labels := by
      have ha : raw19783step2 = (fun i j => raw19783step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19783step2 raw19783step1; decide +kernel
      have hl : raw19783step2Labels = raw19783step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19783step1 raw19783step1Labels permutation29 permutation6
    mixedMoment B raw19783step2 raw19783step2Labels = mixedMoment B raw19783step3 raw19783step3Labels := by
      have ha : raw19783step3 = -raw19783step2 := by apply Matrix.ext; change ∀ i j, raw19783step3 i j = -(raw19783step2 i j); unfold raw19783step3 raw19783step2; decide +kernel
      have hl : raw19783step3Labels = raw19783step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node994 node994Labels := by rfl

def raw19784 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19784step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19784 raw19784Labels = mixedMoment B node986 node986Labels := by
  calc
    mixedMoment B raw19784 raw19784Labels = mixedMoment B raw19784step0 raw19784step0Labels := by
      have hz : ∀ j, raw19784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19784step0 = (fun i j => raw19784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19784step0 raw19784; decide +kernel
      have hl : raw19784step0Labels = raw19784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19784 raw19784Labels permutation346 hz
    mixedMoment B raw19784step0 raw19784step0Labels = mixedMoment B raw19784step1 raw19784step1Labels := by
      have hz : ∀ j, raw19784step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19784step1 = (fun i j => raw19784step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19784step1 raw19784step0; decide +kernel
      have hl : raw19784step1Labels = raw19784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19784step0 raw19784step0Labels permutation56 hz
    mixedMoment B raw19784step1 raw19784step1Labels = mixedMoment B raw19784step2 raw19784step2Labels := by
      have ha : raw19784step2 = (fun i j => raw19784step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19784step2 raw19784step1; decide +kernel
      have hl : raw19784step2Labels = raw19784step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19784step1 raw19784step1Labels permutation10 permutation6
    _ = mixedMoment B node986 node986Labels := by rfl

def raw19785 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19785 raw19785Labels = mixedMoment B node975 node975Labels := by
  calc
    mixedMoment B raw19785 raw19785Labels = mixedMoment B raw19785step0 raw19785step0Labels := by
      have hz : ∀ j, raw19785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19785step0 = (fun i j => raw19785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19785step0 raw19785; decide +kernel
      have hl : raw19785step0Labels = raw19785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19785 raw19785Labels permutation346 hz
    mixedMoment B raw19785step0 raw19785step0Labels = mixedMoment B raw19785step1 raw19785step1Labels := by
      have ha : raw19785step1 = (fun i j => raw19785step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19785step1 raw19785step0; decide +kernel
      have hl : raw19785step1Labels = raw19785step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19785step0 raw19785step0Labels permutation143 permutation6
    mixedMoment B raw19785step1 raw19785step1Labels = mixedMoment B raw19785step2 raw19785step2Labels := by
      have ha : raw19785step2 = -raw19785step1 := by apply Matrix.ext; change ∀ i j, raw19785step2 i j = -(raw19785step1 i j); unfold raw19785step2 raw19785step1; decide +kernel
      have hl : raw19785step2Labels = raw19785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node975 node975Labels := by rfl

def raw19786 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19786 raw19786Labels = mixedMoment B node975 node975Labels := by
  calc
    mixedMoment B raw19786 raw19786Labels = mixedMoment B raw19786step0 raw19786step0Labels := by
      have hz : ∀ j, raw19786 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19786step0 = (fun i j => raw19786 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19786step0 raw19786; decide +kernel
      have hl : raw19786step0Labels = raw19786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19786 raw19786Labels permutation265 hz
    mixedMoment B raw19786step0 raw19786step0Labels = mixedMoment B raw19786step1 raw19786step1Labels := by
      have ha : raw19786step1 = (fun i j => raw19786step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19786step1 raw19786step0; decide +kernel
      have hl : raw19786step1Labels = raw19786step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19786step0 raw19786step0Labels permutation143 permutation6
    mixedMoment B raw19786step1 raw19786step1Labels = mixedMoment B raw19786step2 raw19786step2Labels := by
      have ha : raw19786step2 = -raw19786step1 := by apply Matrix.ext; change ∀ i j, raw19786step2 i j = -(raw19786step1 i j); unfold raw19786step2 raw19786step1; decide +kernel
      have hl : raw19786step2Labels = raw19786step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node975 node975Labels := by rfl

def raw19787 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19787step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw19787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw19787step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19787 raw19787Labels = mixedMoment B node994 node994Labels := by
  calc
    mixedMoment B raw19787 raw19787Labels = mixedMoment B raw19787step0 raw19787step0Labels := by
      have hz : ∀ j, raw19787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19787step0 = (fun i j => raw19787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19787step0 raw19787; decide +kernel
      have hl : raw19787step0Labels = raw19787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19787 raw19787Labels permutation346 hz
    mixedMoment B raw19787step0 raw19787step0Labels = mixedMoment B raw19787step1 raw19787step1Labels := by
      have hz : ∀ j, raw19787step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19787step1 = (fun i j => raw19787step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19787step1 raw19787step0; decide +kernel
      have hl : raw19787step1Labels = raw19787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19787step0 raw19787step0Labels permutation56 hz
    mixedMoment B raw19787step1 raw19787step1Labels = mixedMoment B raw19787step2 raw19787step2Labels := by
      have ha : raw19787step2 = (fun i j => raw19787step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19787step2 raw19787step1; decide +kernel
      have hl : raw19787step2Labels = raw19787step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19787step1 raw19787step1Labels permutation29 permutation6
    mixedMoment B raw19787step2 raw19787step2Labels = mixedMoment B raw19787step3 raw19787step3Labels := by
      have ha : raw19787step3 = -raw19787step2 := by apply Matrix.ext; change ∀ i j, raw19787step3 i j = -(raw19787step2 i j); unfold raw19787step3 raw19787step2; decide +kernel
      have hl : raw19787step3Labels = raw19787step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node994 node994Labels := by rfl

def raw19788 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19788step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19788step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, -2, 4]]
def raw19788step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19788step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 2, -4], ![-2, -2, 4]]
def raw19788step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19788step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw19788step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19788 raw19788Labels = mixedMoment B node1313 node1313Labels := by
  calc
    mixedMoment B raw19788 raw19788Labels = mixedMoment B raw19788step0 raw19788step0Labels := by
      have hz : ∀ j, raw19788 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19788step0 = (fun i j => raw19788 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19788step0 raw19788; decide +kernel
      have hl : raw19788step0Labels = raw19788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19788 raw19788Labels permutation520 hz
    mixedMoment B raw19788step0 raw19788step0Labels = mixedMoment B raw19788step1 raw19788step1Labels := by
      have hz : ∀ j, raw19788step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19788step1 = (fun i j => raw19788step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19788step1 raw19788step0; decide +kernel
      have hl : raw19788step1Labels = raw19788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19788step0 raw19788step0Labels permutation104 hz
    mixedMoment B raw19788step1 raw19788step1Labels = mixedMoment B raw19788step2 raw19788step2Labels := by
      have hz : ∀ j, raw19788step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19788step2 = (fun i j => raw19788step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19788step2 raw19788step1; decide +kernel
      have hl : raw19788step2Labels = raw19788step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19788step1 raw19788step1Labels permutation20 hz
    mixedMoment B raw19788step2 raw19788step2Labels = mixedMoment B raw19788step3 raw19788step3Labels := by
      have hz : ∀ j, raw19788step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19788step3 = (fun i j => raw19788step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19788step3 raw19788step2; decide +kernel
      have hl : raw19788step3Labels = raw19788step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19788step2 raw19788step2Labels permutation4 hz
    mixedMoment B raw19788step3 raw19788step3Labels = mixedMoment B raw19788step4 raw19788step4Labels := by
      have ha : raw19788step4 = (fun i j => raw19788step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19788step4 raw19788step3; decide +kernel
      have hl : raw19788step4Labels = raw19788step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19788step3 raw19788step3Labels permutation0 permutation6
    _ = mixedMoment B node1313 node1313Labels := by rfl

def raw19789 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19789step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19789step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19789step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19789step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-4, 1, 3]]
def raw19789step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19789step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19789step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19789 raw19789Labels = mixedMoment B node817 node817Labels := by
  calc
    mixedMoment B raw19789 raw19789Labels = mixedMoment B raw19789step0 raw19789step0Labels := by
      have hz : ∀ j, raw19789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19789step0 = (fun i j => raw19789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19789step0 raw19789; decide +kernel
      have hl : raw19789step0Labels = raw19789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19789 raw19789Labels permutation434 hz
    mixedMoment B raw19789step0 raw19789step0Labels = mixedMoment B raw19789step1 raw19789step1Labels := by
      have hz : ∀ j, raw19789step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19789step1 = (fun i j => raw19789step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19789step1 raw19789step0; decide +kernel
      have hl : raw19789step1Labels = raw19789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19789step0 raw19789step0Labels permutation80 hz
    mixedMoment B raw19789step1 raw19789step1Labels = mixedMoment B raw19789step2 raw19789step2Labels := by
      have hz : ∀ j, raw19789step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19789step2 = (fun i j => raw19789step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19789step2 raw19789step1; decide +kernel
      have hl : raw19789step2Labels = raw19789step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19789step1 raw19789step1Labels permutation14 hz
    mixedMoment B raw19789step2 raw19789step2Labels = mixedMoment B raw19789step3 raw19789step3Labels := by
      have ha : raw19789step3 = (fun i j => raw19789step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19789step3 raw19789step2; decide +kernel
      have hl : raw19789step3Labels = raw19789step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19789step2 raw19789step2Labels permutation7 permutation6
    mixedMoment B raw19789step3 raw19789step3Labels = mixedMoment B raw19789step4 raw19789step4Labels := by
      have ha : raw19789step4 = -raw19789step3 := by apply Matrix.ext; change ∀ i j, raw19789step4 i j = -(raw19789step3 i j); unfold raw19789step4 raw19789step3; decide +kernel
      have hl : raw19789step4Labels = raw19789step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node817 node817Labels := by rfl

def raw19790 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19790step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19790 raw19790Labels = mixedMoment B node791 node791Labels := by
  calc
    mixedMoment B raw19790 raw19790Labels = mixedMoment B raw19790step0 raw19790step0Labels := by
      have hz : ∀ j, raw19790 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19790step0 = (fun i j => raw19790 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19790step0 raw19790; decide +kernel
      have hl : raw19790step0Labels = raw19790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19790 raw19790Labels permutation434 hz
    mixedMoment B raw19790step0 raw19790step0Labels = mixedMoment B raw19790step1 raw19790step1Labels := by
      have hz : ∀ j, raw19790step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19790step1 = (fun i j => raw19790step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19790step1 raw19790step0; decide +kernel
      have hl : raw19790step1Labels = raw19790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19790step0 raw19790step0Labels permutation80 hz
    mixedMoment B raw19790step1 raw19790step1Labels = mixedMoment B raw19790step2 raw19790step2Labels := by
      have ha : raw19790step2 = (fun i j => raw19790step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19790step2 raw19790step1; decide +kernel
      have hl : raw19790step2Labels = raw19790step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19790step1 raw19790step1Labels permutation29 permutation6
    mixedMoment B raw19790step2 raw19790step2Labels = mixedMoment B raw19790step3 raw19790step3Labels := by
      have ha : raw19790step3 = -raw19790step2 := by apply Matrix.ext; change ∀ i j, raw19790step3 i j = -(raw19790step2 i j); unfold raw19790step3 raw19790step2; decide +kernel
      have hl : raw19790step3Labels = raw19790step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node791 node791Labels := by rfl

def raw19791 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19791step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19791step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19791 raw19791Labels = mixedMoment B node791 node791Labels := by
  calc
    mixedMoment B raw19791 raw19791Labels = mixedMoment B raw19791step0 raw19791step0Labels := by
      have hz : ∀ j, raw19791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19791step0 = (fun i j => raw19791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19791step0 raw19791; decide +kernel
      have hl : raw19791step0Labels = raw19791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19791 raw19791Labels permutation434 hz
    mixedMoment B raw19791step0 raw19791step0Labels = mixedMoment B raw19791step1 raw19791step1Labels := by
      have hz : ∀ j, raw19791step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19791step1 = (fun i j => raw19791step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19791step1 raw19791step0; decide +kernel
      have hl : raw19791step1Labels = raw19791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19791step0 raw19791step0Labels permutation56 hz
    mixedMoment B raw19791step1 raw19791step1Labels = mixedMoment B raw19791step2 raw19791step2Labels := by
      have ha : raw19791step2 = (fun i j => raw19791step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19791step2 raw19791step1; decide +kernel
      have hl : raw19791step2Labels = raw19791step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19791step1 raw19791step1Labels permutation29 permutation6
    mixedMoment B raw19791step2 raw19791step2Labels = mixedMoment B raw19791step3 raw19791step3Labels := by
      have ha : raw19791step3 = -raw19791step2 := by apply Matrix.ext; change ∀ i j, raw19791step3 i j = -(raw19791step2 i j); unfold raw19791step3 raw19791step2; decide +kernel
      have hl : raw19791step3Labels = raw19791step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node791 node791Labels := by rfl

def raw19792 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19792step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19792step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19792step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19792step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19792 raw19792Labels = mixedMoment B node791 node791Labels := by
  calc
    mixedMoment B raw19792 raw19792Labels = mixedMoment B raw19792step0 raw19792step0Labels := by
      have hz : ∀ j, raw19792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19792step0 = (fun i j => raw19792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19792step0 raw19792; decide +kernel
      have hl : raw19792step0Labels = raw19792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19792 raw19792Labels permutation346 hz
    mixedMoment B raw19792step0 raw19792step0Labels = mixedMoment B raw19792step1 raw19792step1Labels := by
      have hz : ∀ j, raw19792step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19792step1 = (fun i j => raw19792step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19792step1 raw19792step0; decide +kernel
      have hl : raw19792step1Labels = raw19792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19792step0 raw19792step0Labels permutation56 hz
    mixedMoment B raw19792step1 raw19792step1Labels = mixedMoment B raw19792step2 raw19792step2Labels := by
      have ha : raw19792step2 = (fun i j => raw19792step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19792step2 raw19792step1; decide +kernel
      have hl : raw19792step2Labels = raw19792step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19792step1 raw19792step1Labels permutation29 permutation6
    mixedMoment B raw19792step2 raw19792step2Labels = mixedMoment B raw19792step3 raw19792step3Labels := by
      have ha : raw19792step3 = -raw19792step2 := by apply Matrix.ext; change ∀ i j, raw19792step3 i j = -(raw19792step2 i j); unfold raw19792step3 raw19792step2; decide +kernel
      have hl : raw19792step3Labels = raw19792step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node791 node791Labels := by rfl

def raw19793 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19793step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19793step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19793step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -4, 4]]
def raw19793step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19793step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-4, 2, 2]]
def raw19793step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19793step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw19793step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19793 raw19793Labels = mixedMoment B node832 node832Labels := by
  calc
    mixedMoment B raw19793 raw19793Labels = mixedMoment B raw19793step0 raw19793step0Labels := by
      have hz : ∀ j, raw19793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19793step0 = (fun i j => raw19793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19793step0 raw19793; decide +kernel
      have hl : raw19793step0Labels = raw19793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19793 raw19793Labels permutation434 hz
    mixedMoment B raw19793step0 raw19793step0Labels = mixedMoment B raw19793step1 raw19793step1Labels := by
      have hz : ∀ j, raw19793step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19793step1 = (fun i j => raw19793step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19793step1 raw19793step0; decide +kernel
      have hl : raw19793step1Labels = raw19793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19793step0 raw19793step0Labels permutation80 hz
    mixedMoment B raw19793step1 raw19793step1Labels = mixedMoment B raw19793step2 raw19793step2Labels := by
      have hz : ∀ j, raw19793step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19793step2 = (fun i j => raw19793step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19793step2 raw19793step1; decide +kernel
      have hl : raw19793step2Labels = raw19793step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19793step1 raw19793step1Labels permutation14 hz
    mixedMoment B raw19793step2 raw19793step2Labels = mixedMoment B raw19793step3 raw19793step3Labels := by
      have ha : raw19793step3 = (fun i j => raw19793step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19793step3 raw19793step2; decide +kernel
      have hl : raw19793step3Labels = raw19793step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19793step2 raw19793step2Labels permutation7 permutation6
    mixedMoment B raw19793step3 raw19793step3Labels = mixedMoment B raw19793step4 raw19793step4Labels := by
      have ha : raw19793step4 = -raw19793step3 := by apply Matrix.ext; change ∀ i j, raw19793step4 i j = -(raw19793step3 i j); unfold raw19793step4 raw19793step3; decide +kernel
      have hl : raw19793step4Labels = raw19793step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node832 node832Labels := by rfl

def raw19794 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19794step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19794step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19794step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19794step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19794step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19794 raw19794Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw19794 raw19794Labels = mixedMoment B raw19794step0 raw19794step0Labels := by
      have hz : ∀ j, raw19794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19794step0 = (fun i j => raw19794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19794step0 raw19794; decide +kernel
      have hl : raw19794step0Labels = raw19794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19794 raw19794Labels permutation434 hz
    mixedMoment B raw19794step0 raw19794step0Labels = mixedMoment B raw19794step1 raw19794step1Labels := by
      have hz : ∀ j, raw19794step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19794step1 = (fun i j => raw19794step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19794step1 raw19794step0; decide +kernel
      have hl : raw19794step1Labels = raw19794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19794step0 raw19794step0Labels permutation80 hz
    mixedMoment B raw19794step1 raw19794step1Labels = mixedMoment B raw19794step2 raw19794step2Labels := by
      have ha : raw19794step2 = (fun i j => raw19794step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19794step2 raw19794step1; decide +kernel
      have hl : raw19794step2Labels = raw19794step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19794step1 raw19794step1Labels permutation8 permutation7
    mixedMoment B raw19794step2 raw19794step2Labels = mixedMoment B raw19794step3 raw19794step3Labels := by
      have ha : raw19794step3 = raw19794step2 := by apply Matrix.ext; unfold raw19794step3 raw19794step2; decide +kernel
      have hl : raw19794step2Labels = labelEmbedding1 ∘ raw19794step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19794step2 raw19794step2Labels raw19794step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1027 node1027Labels := by rfl

def raw19795 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19795step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19795step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19795step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19795 raw19795Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw19795 raw19795Labels = mixedMoment B raw19795step0 raw19795step0Labels := by
      have hz : ∀ j, raw19795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19795step0 = (fun i j => raw19795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19795step0 raw19795; decide +kernel
      have hl : raw19795step0Labels = raw19795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19795 raw19795Labels permutation434 hz
    mixedMoment B raw19795step0 raw19795step0Labels = mixedMoment B raw19795step1 raw19795step1Labels := by
      have hz : ∀ j, raw19795step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19795step1 = (fun i j => raw19795step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19795step1 raw19795step0; decide +kernel
      have hl : raw19795step1Labels = raw19795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19795step0 raw19795step0Labels permutation56 hz
    mixedMoment B raw19795step1 raw19795step1Labels = mixedMoment B raw19795step2 raw19795step2Labels := by
      have ha : raw19795step2 = (fun i j => raw19795step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19795step2 raw19795step1; decide +kernel
      have hl : raw19795step2Labels = raw19795step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19795step1 raw19795step1Labels permutation8 permutation7
    mixedMoment B raw19795step2 raw19795step2Labels = mixedMoment B raw19795step3 raw19795step3Labels := by
      have ha : raw19795step3 = raw19795step2 := by apply Matrix.ext; unfold raw19795step3 raw19795step2; decide +kernel
      have hl : raw19795step2Labels = labelEmbedding1 ∘ raw19795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19795step2 raw19795step2Labels raw19795step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1027 node1027Labels := by rfl

def raw19796 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19796step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19796step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19796step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19796step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19796step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19796step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19796 raw19796Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw19796 raw19796Labels = mixedMoment B raw19796step0 raw19796step0Labels := by
      have hz : ∀ j, raw19796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19796step0 = (fun i j => raw19796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19796step0 raw19796; decide +kernel
      have hl : raw19796step0Labels = raw19796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19796 raw19796Labels permutation346 hz
    mixedMoment B raw19796step0 raw19796step0Labels = mixedMoment B raw19796step1 raw19796step1Labels := by
      have hz : ∀ j, raw19796step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19796step1 = (fun i j => raw19796step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19796step1 raw19796step0; decide +kernel
      have hl : raw19796step1Labels = raw19796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19796step0 raw19796step0Labels permutation56 hz
    mixedMoment B raw19796step1 raw19796step1Labels = mixedMoment B raw19796step2 raw19796step2Labels := by
      have ha : raw19796step2 = (fun i j => raw19796step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19796step2 raw19796step1; decide +kernel
      have hl : raw19796step2Labels = raw19796step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19796step1 raw19796step1Labels permutation8 permutation7
    mixedMoment B raw19796step2 raw19796step2Labels = mixedMoment B raw19796step3 raw19796step3Labels := by
      have ha : raw19796step3 = raw19796step2 := by apply Matrix.ext; unfold raw19796step3 raw19796step2; decide +kernel
      have hl : raw19796step2Labels = labelEmbedding1 ∘ raw19796step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19796step2 raw19796step2Labels raw19796step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1027 node1027Labels := by rfl

def raw19797 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19797step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19797step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, -3, 4]]
def raw19797step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19797step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw19797step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19797step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw19797step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19797 raw19797Labels = mixedMoment B node1064 node1064Labels := by
  calc
    mixedMoment B raw19797 raw19797Labels = mixedMoment B raw19797step0 raw19797step0Labels := by
      have hz : ∀ j, raw19797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19797step0 = (fun i j => raw19797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19797step0 raw19797; decide +kernel
      have hl : raw19797step0Labels = raw19797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19797 raw19797Labels permutation434 hz
    mixedMoment B raw19797step0 raw19797step0Labels = mixedMoment B raw19797step1 raw19797step1Labels := by
      have hz : ∀ j, raw19797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19797step1 = (fun i j => raw19797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19797step1 raw19797step0; decide +kernel
      have hl : raw19797step1Labels = raw19797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19797step0 raw19797step0Labels permutation80 hz
    mixedMoment B raw19797step1 raw19797step1Labels = mixedMoment B raw19797step2 raw19797step2Labels := by
      have hz : ∀ j, raw19797step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19797step2 = (fun i j => raw19797step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19797step2 raw19797step1; decide +kernel
      have hl : raw19797step2Labels = raw19797step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19797step1 raw19797step1Labels permutation14 hz
    mixedMoment B raw19797step2 raw19797step2Labels = mixedMoment B raw19797step3 raw19797step3Labels := by
      have ha : raw19797step3 = (fun i j => raw19797step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19797step3 raw19797step2; decide +kernel
      have hl : raw19797step3Labels = raw19797step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19797step2 raw19797step2Labels permutation2 permutation7
    mixedMoment B raw19797step3 raw19797step3Labels = mixedMoment B raw19797step4 raw19797step4Labels := by
      have ha : raw19797step4 = raw19797step3 := by apply Matrix.ext; unfold raw19797step4 raw19797step3; decide +kernel
      have hl : raw19797step3Labels = labelEmbedding1 ∘ raw19797step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19797step3 raw19797step3Labels raw19797step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1064 node1064Labels := by rfl

def raw19798 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19798step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19798step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19798step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19798step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19798step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19798step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19798step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19798step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19798 raw19798Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw19798 raw19798Labels = mixedMoment B raw19798step0 raw19798step0Labels := by
      have hz : ∀ j, raw19798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19798step0 = (fun i j => raw19798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19798step0 raw19798; decide +kernel
      have hl : raw19798step0Labels = raw19798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19798 raw19798Labels permutation434 hz
    mixedMoment B raw19798step0 raw19798step0Labels = mixedMoment B raw19798step1 raw19798step1Labels := by
      have hz : ∀ j, raw19798step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19798step1 = (fun i j => raw19798step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19798step1 raw19798step0; decide +kernel
      have hl : raw19798step1Labels = raw19798step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19798step0 raw19798step0Labels permutation80 hz
    mixedMoment B raw19798step1 raw19798step1Labels = mixedMoment B raw19798step2 raw19798step2Labels := by
      have hz : ∀ j, raw19798step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19798step2 = (fun i j => raw19798step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19798step2 raw19798step1; decide +kernel
      have hl : raw19798step2Labels = raw19798step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19798step1 raw19798step1Labels permutation14 hz
    mixedMoment B raw19798step2 raw19798step2Labels = mixedMoment B raw19798step3 raw19798step3Labels := by
      have ha : raw19798step3 = (fun i j => raw19798step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19798step3 raw19798step2; decide +kernel
      have hl : raw19798step3Labels = raw19798step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19798step2 raw19798step2Labels permutation2 permutation7
    mixedMoment B raw19798step3 raw19798step3Labels = mixedMoment B raw19798step4 raw19798step4Labels := by
      have ha : raw19798step4 = raw19798step3 := by apply Matrix.ext; unfold raw19798step4 raw19798step3; decide +kernel
      have hl : raw19798step3Labels = labelEmbedding1 ∘ raw19798step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19798step3 raw19798step3Labels raw19798step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw19799 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19799step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19799step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw19799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19799step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw19799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19799 raw19799Labels = mixedMoment B node1402 node1402Labels := by
  calc
    mixedMoment B raw19799 raw19799Labels = mixedMoment B raw19799step0 raw19799step0Labels := by
      have hz : ∀ j, raw19799 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19799step0 = (fun i j => raw19799 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19799step0 raw19799; decide +kernel
      have hl : raw19799step0Labels = raw19799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19799 raw19799Labels permutation434 hz
    mixedMoment B raw19799step0 raw19799step0Labels = mixedMoment B raw19799step1 raw19799step1Labels := by
      have hz : ∀ j, raw19799step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19799step1 = (fun i j => raw19799step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19799step1 raw19799step0; decide +kernel
      have hl : raw19799step1Labels = raw19799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19799step0 raw19799step0Labels permutation80 hz
    mixedMoment B raw19799step1 raw19799step1Labels = mixedMoment B raw19799step2 raw19799step2Labels := by
      have ha : raw19799step2 = (fun i j => raw19799step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19799step2 raw19799step1; decide +kernel
      have hl : raw19799step2Labels = raw19799step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19799step1 raw19799step1Labels permutation8 permutation7
    mixedMoment B raw19799step2 raw19799step2Labels = mixedMoment B raw19799step3 raw19799step3Labels := by
      have ha : raw19799step3 = raw19799step2 := by apply Matrix.ext; unfold raw19799step3 raw19799step2; decide +kernel
      have hl : raw19799step2Labels = labelEmbedding1 ∘ raw19799step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19799step2 raw19799step2Labels raw19799step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1402 node1402Labels := by rfl

def raw19800 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19800 raw19800Labels = mixedMoment B node1209 node1209Labels := by
  calc
    mixedMoment B raw19800 raw19800Labels = mixedMoment B raw19800step0 raw19800step0Labels := by
      have hz : ∀ j, raw19800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19800step0 = (fun i j => raw19800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19800step0 raw19800; decide +kernel
      have hl : raw19800step0Labels = raw19800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19800 raw19800Labels permutation434 hz
    mixedMoment B raw19800step0 raw19800step0Labels = mixedMoment B raw19800step1 raw19800step1Labels := by
      have ha : raw19800step1 = (fun i j => raw19800step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19800step1 raw19800step0; decide +kernel
      have hl : raw19800step1Labels = raw19800step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19800step0 raw19800step0Labels permutation32 permutation7
    mixedMoment B raw19800step1 raw19800step1Labels = mixedMoment B raw19800step2 raw19800step2Labels := by
      have ha : raw19800step2 = raw19800step1 := by apply Matrix.ext; unfold raw19800step2 raw19800step1; decide +kernel
      have hl : raw19800step1Labels = labelEmbedding1 ∘ raw19800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19800step1 raw19800step1Labels raw19800step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1209 node1209Labels := by rfl

def raw19801 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19801 raw19801Labels = mixedMoment B node1209 node1209Labels := by
  calc
    mixedMoment B raw19801 raw19801Labels = mixedMoment B raw19801step0 raw19801step0Labels := by
      have hz : ∀ j, raw19801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19801step0 = (fun i j => raw19801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19801step0 raw19801; decide +kernel
      have hl : raw19801step0Labels = raw19801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19801 raw19801Labels permutation346 hz
    mixedMoment B raw19801step0 raw19801step0Labels = mixedMoment B raw19801step1 raw19801step1Labels := by
      have ha : raw19801step1 = (fun i j => raw19801step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19801step1 raw19801step0; decide +kernel
      have hl : raw19801step1Labels = raw19801step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19801step0 raw19801step0Labels permutation32 permutation7
    mixedMoment B raw19801step1 raw19801step1Labels = mixedMoment B raw19801step2 raw19801step2Labels := by
      have ha : raw19801step2 = raw19801step1 := by apply Matrix.ext; unfold raw19801step2 raw19801step1; decide +kernel
      have hl : raw19801step1Labels = labelEmbedding1 ∘ raw19801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19801step1 raw19801step1Labels raw19801step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1209 node1209Labels := by rfl

def raw19802 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19802step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19802step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw19802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw19802step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19802 raw19802Labels = mixedMoment B node1227 node1227Labels := by
  calc
    mixedMoment B raw19802 raw19802Labels = mixedMoment B raw19802step0 raw19802step0Labels := by
      have hz : ∀ j, raw19802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19802step0 = (fun i j => raw19802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19802step0 raw19802; decide +kernel
      have hl : raw19802step0Labels = raw19802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19802 raw19802Labels permutation434 hz
    mixedMoment B raw19802step0 raw19802step0Labels = mixedMoment B raw19802step1 raw19802step1Labels := by
      have hz : ∀ j, raw19802step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19802step1 = (fun i j => raw19802step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19802step1 raw19802step0; decide +kernel
      have hl : raw19802step1Labels = raw19802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19802step0 raw19802step0Labels permutation80 hz
    mixedMoment B raw19802step1 raw19802step1Labels = mixedMoment B raw19802step2 raw19802step2Labels := by
      have ha : raw19802step2 = (fun i j => raw19802step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19802step2 raw19802step1; decide +kernel
      have hl : raw19802step2Labels = raw19802step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19802step1 raw19802step1Labels permutation8 permutation7
    mixedMoment B raw19802step2 raw19802step2Labels = mixedMoment B raw19802step3 raw19802step3Labels := by
      have ha : raw19802step3 = raw19802step2 := by apply Matrix.ext; unfold raw19802step3 raw19802step2; decide +kernel
      have hl : raw19802step2Labels = labelEmbedding1 ∘ raw19802step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19802step2 raw19802step2Labels raw19802step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1227 node1227Labels := by rfl

def raw19803 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19803step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19803step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19803step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19803 raw19803Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19803 raw19803Labels = mixedMoment B raw19803step0 raw19803step0Labels := by
      have hz : ∀ j, raw19803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19803step0 = (fun i j => raw19803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19803step0 raw19803; decide +kernel
      have hl : raw19803step0Labels = raw19803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19803 raw19803Labels permutation434 hz
    mixedMoment B raw19803step0 raw19803step0Labels = mixedMoment B raw19803step1 raw19803step1Labels := by
      have hz : ∀ j, raw19803step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19803step1 = (fun i j => raw19803step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19803step1 raw19803step0; decide +kernel
      have hl : raw19803step1Labels = raw19803step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19803step0 raw19803step0Labels permutation80 hz
    mixedMoment B raw19803step1 raw19803step1Labels = mixedMoment B raw19803step2 raw19803step2Labels := by
      have ha : raw19803step2 = (fun i j => raw19803step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19803step2 raw19803step1; decide +kernel
      have hl : raw19803step2Labels = raw19803step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19803step1 raw19803step1Labels permutation8 permutation7
    mixedMoment B raw19803step2 raw19803step2Labels = mixedMoment B raw19803step3 raw19803step3Labels := by
      have ha : raw19803step3 = raw19803step2 := by apply Matrix.ext; unfold raw19803step3 raw19803step2; decide +kernel
      have hl : raw19803step2Labels = labelEmbedding1 ∘ raw19803step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19803step2 raw19803step2Labels raw19803step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19804 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19804step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw19804step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19804step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw19804step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19804 raw19804Labels = mixedMoment B node1402 node1402Labels := by
  calc
    mixedMoment B raw19804 raw19804Labels = mixedMoment B raw19804step0 raw19804step0Labels := by
      have hz : ∀ j, raw19804 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19804step0 = (fun i j => raw19804 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19804step0 raw19804; decide +kernel
      have hl : raw19804step0Labels = raw19804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19804 raw19804Labels permutation434 hz
    mixedMoment B raw19804step0 raw19804step0Labels = mixedMoment B raw19804step1 raw19804step1Labels := by
      have hz : ∀ j, raw19804step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19804step1 = (fun i j => raw19804step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19804step1 raw19804step0; decide +kernel
      have hl : raw19804step1Labels = raw19804step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19804step0 raw19804step0Labels permutation56 hz
    mixedMoment B raw19804step1 raw19804step1Labels = mixedMoment B raw19804step2 raw19804step2Labels := by
      have ha : raw19804step2 = (fun i j => raw19804step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19804step2 raw19804step1; decide +kernel
      have hl : raw19804step2Labels = raw19804step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19804step1 raw19804step1Labels permutation8 permutation7
    mixedMoment B raw19804step2 raw19804step2Labels = mixedMoment B raw19804step3 raw19804step3Labels := by
      have ha : raw19804step3 = raw19804step2 := by apply Matrix.ext; unfold raw19804step3 raw19804step2; decide +kernel
      have hl : raw19804step2Labels = labelEmbedding1 ∘ raw19804step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19804step2 raw19804step2Labels raw19804step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1402 node1402Labels := by rfl

def raw19805 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19805 raw19805Labels = mixedMoment B node1209 node1209Labels := by
  calc
    mixedMoment B raw19805 raw19805Labels = mixedMoment B raw19805step0 raw19805step0Labels := by
      have hz : ∀ j, raw19805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19805step0 = (fun i j => raw19805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19805step0 raw19805; decide +kernel
      have hl : raw19805step0Labels = raw19805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19805 raw19805Labels permutation434 hz
    mixedMoment B raw19805step0 raw19805step0Labels = mixedMoment B raw19805step1 raw19805step1Labels := by
      have ha : raw19805step1 = (fun i j => raw19805step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19805step1 raw19805step0; decide +kernel
      have hl : raw19805step1Labels = raw19805step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19805step0 raw19805step0Labels permutation38 permutation7
    mixedMoment B raw19805step1 raw19805step1Labels = mixedMoment B raw19805step2 raw19805step2Labels := by
      have ha : raw19805step2 = raw19805step1 := by apply Matrix.ext; unfold raw19805step2 raw19805step1; decide +kernel
      have hl : raw19805step1Labels = labelEmbedding1 ∘ raw19805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19805step1 raw19805step1Labels raw19805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1209 node1209Labels := by rfl

def raw19806 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19806 raw19806Labels = mixedMoment B node1209 node1209Labels := by
  calc
    mixedMoment B raw19806 raw19806Labels = mixedMoment B raw19806step0 raw19806step0Labels := by
      have hz : ∀ j, raw19806 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19806step0 = (fun i j => raw19806 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19806step0 raw19806; decide +kernel
      have hl : raw19806step0Labels = raw19806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19806 raw19806Labels permutation265 hz
    mixedMoment B raw19806step0 raw19806step0Labels = mixedMoment B raw19806step1 raw19806step1Labels := by
      have ha : raw19806step1 = (fun i j => raw19806step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19806step1 raw19806step0; decide +kernel
      have hl : raw19806step1Labels = raw19806step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19806step0 raw19806step0Labels permutation32 permutation7
    mixedMoment B raw19806step1 raw19806step1Labels = mixedMoment B raw19806step2 raw19806step2Labels := by
      have ha : raw19806step2 = raw19806step1 := by apply Matrix.ext; unfold raw19806step2 raw19806step1; decide +kernel
      have hl : raw19806step1Labels = labelEmbedding1 ∘ raw19806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19806step1 raw19806step1Labels raw19806step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1209 node1209Labels := by rfl

def raw19807 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19807step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19807step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19807step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw19807step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19807step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw19807step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19807 raw19807Labels = mixedMoment B node1227 node1227Labels := by
  calc
    mixedMoment B raw19807 raw19807Labels = mixedMoment B raw19807step0 raw19807step0Labels := by
      have hz : ∀ j, raw19807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19807step0 = (fun i j => raw19807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19807step0 raw19807; decide +kernel
      have hl : raw19807step0Labels = raw19807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19807 raw19807Labels permutation434 hz
    mixedMoment B raw19807step0 raw19807step0Labels = mixedMoment B raw19807step1 raw19807step1Labels := by
      have hz : ∀ j, raw19807step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19807step1 = (fun i j => raw19807step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19807step1 raw19807step0; decide +kernel
      have hl : raw19807step1Labels = raw19807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19807step0 raw19807step0Labels permutation56 hz
    mixedMoment B raw19807step1 raw19807step1Labels = mixedMoment B raw19807step2 raw19807step2Labels := by
      have ha : raw19807step2 = (fun i j => raw19807step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19807step2 raw19807step1; decide +kernel
      have hl : raw19807step2Labels = raw19807step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19807step1 raw19807step1Labels permutation8 permutation7
    mixedMoment B raw19807step2 raw19807step2Labels = mixedMoment B raw19807step3 raw19807step3Labels := by
      have ha : raw19807step3 = raw19807step2 := by apply Matrix.ext; unfold raw19807step3 raw19807step2; decide +kernel
      have hl : raw19807step2Labels = labelEmbedding1 ∘ raw19807step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19807step2 raw19807step2Labels raw19807step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1227 node1227Labels := by rfl

def raw19808 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19808step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19808step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19808 raw19808Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19808 raw19808Labels = mixedMoment B raw19808step0 raw19808step0Labels := by
      have hz : ∀ j, raw19808 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19808step0 = (fun i j => raw19808 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19808step0 raw19808; decide +kernel
      have hl : raw19808step0Labels = raw19808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19808 raw19808Labels permutation434 hz
    mixedMoment B raw19808step0 raw19808step0Labels = mixedMoment B raw19808step1 raw19808step1Labels := by
      have hz : ∀ j, raw19808step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19808step1 = (fun i j => raw19808step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19808step1 raw19808step0; decide +kernel
      have hl : raw19808step1Labels = raw19808step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19808step0 raw19808step0Labels permutation56 hz
    mixedMoment B raw19808step1 raw19808step1Labels = mixedMoment B raw19808step2 raw19808step2Labels := by
      have ha : raw19808step2 = (fun i j => raw19808step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19808step2 raw19808step1; decide +kernel
      have hl : raw19808step2Labels = raw19808step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19808step1 raw19808step1Labels permutation8 permutation7
    mixedMoment B raw19808step2 raw19808step2Labels = mixedMoment B raw19808step3 raw19808step3Labels := by
      have ha : raw19808step3 = raw19808step2 := by apply Matrix.ext; unfold raw19808step3 raw19808step2; decide +kernel
      have hl : raw19808step2Labels = labelEmbedding1 ∘ raw19808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19808step2 raw19808step2Labels raw19808step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19809 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19809step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw19809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19809step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw19809step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19809 raw19809Labels = mixedMoment B node1402 node1402Labels := by
  calc
    mixedMoment B raw19809 raw19809Labels = mixedMoment B raw19809step0 raw19809step0Labels := by
      have hz : ∀ j, raw19809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19809step0 = (fun i j => raw19809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19809step0 raw19809; decide +kernel
      have hl : raw19809step0Labels = raw19809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19809 raw19809Labels permutation346 hz
    mixedMoment B raw19809step0 raw19809step0Labels = mixedMoment B raw19809step1 raw19809step1Labels := by
      have hz : ∀ j, raw19809step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19809step1 = (fun i j => raw19809step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19809step1 raw19809step0; decide +kernel
      have hl : raw19809step1Labels = raw19809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19809step0 raw19809step0Labels permutation56 hz
    mixedMoment B raw19809step1 raw19809step1Labels = mixedMoment B raw19809step2 raw19809step2Labels := by
      have ha : raw19809step2 = (fun i j => raw19809step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19809step2 raw19809step1; decide +kernel
      have hl : raw19809step2Labels = raw19809step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19809step1 raw19809step1Labels permutation8 permutation7
    mixedMoment B raw19809step2 raw19809step2Labels = mixedMoment B raw19809step3 raw19809step3Labels := by
      have ha : raw19809step3 = raw19809step2 := by apply Matrix.ext; unfold raw19809step3 raw19809step2; decide +kernel
      have hl : raw19809step2Labels = labelEmbedding1 ∘ raw19809step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19809step2 raw19809step2Labels raw19809step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1402 node1402Labels := by rfl

def raw19810 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19810step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19810 raw19810Labels = mixedMoment B node1209 node1209Labels := by
  calc
    mixedMoment B raw19810 raw19810Labels = mixedMoment B raw19810step0 raw19810step0Labels := by
      have hz : ∀ j, raw19810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19810step0 = (fun i j => raw19810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19810step0 raw19810; decide +kernel
      have hl : raw19810step0Labels = raw19810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19810 raw19810Labels permutation346 hz
    mixedMoment B raw19810step0 raw19810step0Labels = mixedMoment B raw19810step1 raw19810step1Labels := by
      have ha : raw19810step1 = (fun i j => raw19810step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19810step1 raw19810step0; decide +kernel
      have hl : raw19810step1Labels = raw19810step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19810step0 raw19810step0Labels permutation38 permutation7
    mixedMoment B raw19810step1 raw19810step1Labels = mixedMoment B raw19810step2 raw19810step2Labels := by
      have ha : raw19810step2 = raw19810step1 := by apply Matrix.ext; unfold raw19810step2 raw19810step1; decide +kernel
      have hl : raw19810step1Labels = labelEmbedding1 ∘ raw19810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19810step1 raw19810step1Labels raw19810step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1209 node1209Labels := by rfl

def raw19811 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19811step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19811 raw19811Labels = mixedMoment B node1209 node1209Labels := by
  calc
    mixedMoment B raw19811 raw19811Labels = mixedMoment B raw19811step0 raw19811step0Labels := by
      have hz : ∀ j, raw19811 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19811step0 = (fun i j => raw19811 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19811step0 raw19811; decide +kernel
      have hl : raw19811step0Labels = raw19811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19811 raw19811Labels permutation265 hz
    mixedMoment B raw19811step0 raw19811step0Labels = mixedMoment B raw19811step1 raw19811step1Labels := by
      have ha : raw19811step1 = (fun i j => raw19811step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19811step1 raw19811step0; decide +kernel
      have hl : raw19811step1Labels = raw19811step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19811step0 raw19811step0Labels permutation38 permutation7
    mixedMoment B raw19811step1 raw19811step1Labels = mixedMoment B raw19811step2 raw19811step2Labels := by
      have ha : raw19811step2 = raw19811step1 := by apply Matrix.ext; unfold raw19811step2 raw19811step1; decide +kernel
      have hl : raw19811step1Labels = labelEmbedding1 ∘ raw19811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19811step1 raw19811step1Labels raw19811step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1209 node1209Labels := by rfl

def raw19812 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19812step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19812step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, -3, 4]]
def raw19812step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19812step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw19812step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19812step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw19812step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19812 raw19812Labels = mixedMoment B node1227 node1227Labels := by
  calc
    mixedMoment B raw19812 raw19812Labels = mixedMoment B raw19812step0 raw19812step0Labels := by
      have hz : ∀ j, raw19812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19812step0 = (fun i j => raw19812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19812step0 raw19812; decide +kernel
      have hl : raw19812step0Labels = raw19812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19812 raw19812Labels permutation346 hz
    mixedMoment B raw19812step0 raw19812step0Labels = mixedMoment B raw19812step1 raw19812step1Labels := by
      have hz : ∀ j, raw19812step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19812step1 = (fun i j => raw19812step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19812step1 raw19812step0; decide +kernel
      have hl : raw19812step1Labels = raw19812step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19812step0 raw19812step0Labels permutation56 hz
    mixedMoment B raw19812step1 raw19812step1Labels = mixedMoment B raw19812step2 raw19812step2Labels := by
      have ha : raw19812step2 = (fun i j => raw19812step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19812step2 raw19812step1; decide +kernel
      have hl : raw19812step2Labels = raw19812step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19812step1 raw19812step1Labels permutation8 permutation7
    mixedMoment B raw19812step2 raw19812step2Labels = mixedMoment B raw19812step3 raw19812step3Labels := by
      have ha : raw19812step3 = raw19812step2 := by apply Matrix.ext; unfold raw19812step3 raw19812step2; decide +kernel
      have hl : raw19812step2Labels = labelEmbedding1 ∘ raw19812step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19812step2 raw19812step2Labels raw19812step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1227 node1227Labels := by rfl

def raw19813 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19813step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19813step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19813step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19813 raw19813Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19813 raw19813Labels = mixedMoment B raw19813step0 raw19813step0Labels := by
      have hz : ∀ j, raw19813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19813step0 = (fun i j => raw19813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19813step0 raw19813; decide +kernel
      have hl : raw19813step0Labels = raw19813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19813 raw19813Labels permutation346 hz
    mixedMoment B raw19813step0 raw19813step0Labels = mixedMoment B raw19813step1 raw19813step1Labels := by
      have hz : ∀ j, raw19813step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19813step1 = (fun i j => raw19813step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19813step1 raw19813step0; decide +kernel
      have hl : raw19813step1Labels = raw19813step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19813step0 raw19813step0Labels permutation56 hz
    mixedMoment B raw19813step1 raw19813step1Labels = mixedMoment B raw19813step2 raw19813step2Labels := by
      have ha : raw19813step2 = (fun i j => raw19813step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19813step2 raw19813step1; decide +kernel
      have hl : raw19813step2Labels = raw19813step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19813step1 raw19813step1Labels permutation8 permutation7
    mixedMoment B raw19813step2 raw19813step2Labels = mixedMoment B raw19813step3 raw19813step3Labels := by
      have ha : raw19813step3 = raw19813step2 := by apply Matrix.ext; unfold raw19813step3 raw19813step2; decide +kernel
      have hl : raw19813step2Labels = labelEmbedding1 ∘ raw19813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19813step2 raw19813step2Labels raw19813step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19814 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19814step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19814step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -3, 4]]
def raw19814step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19814step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -3, 4]]
def raw19814step3Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19814step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 3, 1], ![4, -3, -1]]
def raw19814step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19814step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 3, 1], ![4, -3, -1]]
def raw19814step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19814 raw19814Labels = mixedMoment B node1456 node1456Labels := by
  calc
    mixedMoment B raw19814 raw19814Labels = mixedMoment B raw19814step0 raw19814step0Labels := by
      have hz : ∀ j, raw19814 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19814step0 = (fun i j => raw19814 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19814step0 raw19814; decide +kernel
      have hl : raw19814step0Labels = raw19814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19814 raw19814Labels permutation520 hz
    mixedMoment B raw19814step0 raw19814step0Labels = mixedMoment B raw19814step1 raw19814step1Labels := by
      have hz : ∀ j, raw19814step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19814step1 = (fun i j => raw19814step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19814step1 raw19814step0; decide +kernel
      have hl : raw19814step1Labels = raw19814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19814step0 raw19814step0Labels permutation104 hz
    mixedMoment B raw19814step1 raw19814step1Labels = mixedMoment B raw19814step2 raw19814step2Labels := by
      have hz : ∀ j, raw19814step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19814step2 = (fun i j => raw19814step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19814step2 raw19814step1; decide +kernel
      have hl : raw19814step2Labels = raw19814step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19814step1 raw19814step1Labels permutation20 hz
    mixedMoment B raw19814step2 raw19814step2Labels = mixedMoment B raw19814step3 raw19814step3Labels := by
      have hz : ∀ j, raw19814step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19814step3 = (fun i j => raw19814step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19814step3 raw19814step2; decide +kernel
      have hl : raw19814step3Labels = raw19814step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19814step2 raw19814step2Labels permutation4 hz
    mixedMoment B raw19814step3 raw19814step3Labels = mixedMoment B raw19814step4 raw19814step4Labels := by
      have ha : raw19814step4 = (fun i j => raw19814step3 (permutation0 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19814step4 raw19814step3; decide +kernel
      have hl : raw19814step4Labels = raw19814step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19814step3 raw19814step3Labels permutation0 permutation7
    mixedMoment B raw19814step4 raw19814step4Labels = mixedMoment B raw19814step5 raw19814step5Labels := by
      have ha : raw19814step5 = raw19814step4 := by apply Matrix.ext; unfold raw19814step5 raw19814step4; decide +kernel
      have hl : raw19814step4Labels = labelEmbedding1 ∘ raw19814step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19814step4 raw19814step4Labels raw19814step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1456 node1456Labels := by rfl

def raw19815 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19815step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19815step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19815step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19815step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19815step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19815step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19815step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19815 raw19815Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw19815 raw19815Labels = mixedMoment B raw19815step0 raw19815step0Labels := by
      have hz : ∀ j, raw19815 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19815step0 = (fun i j => raw19815 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19815step0 raw19815; decide +kernel
      have hl : raw19815step0Labels = raw19815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19815 raw19815Labels permutation520 hz
    mixedMoment B raw19815step0 raw19815step0Labels = mixedMoment B raw19815step1 raw19815step1Labels := by
      have hz : ∀ j, raw19815step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19815step1 = (fun i j => raw19815step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19815step1 raw19815step0; decide +kernel
      have hl : raw19815step1Labels = raw19815step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19815step0 raw19815step0Labels permutation104 hz
    mixedMoment B raw19815step1 raw19815step1Labels = mixedMoment B raw19815step2 raw19815step2Labels := by
      have hz : ∀ j, raw19815step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19815step2 = (fun i j => raw19815step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19815step2 raw19815step1; decide +kernel
      have hl : raw19815step2Labels = raw19815step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19815step1 raw19815step1Labels permutation20 hz
    mixedMoment B raw19815step2 raw19815step2Labels = mixedMoment B raw19815step3 raw19815step3Labels := by
      have ha : raw19815step3 = (fun i j => raw19815step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19815step3 raw19815step2; decide +kernel
      have hl : raw19815step3Labels = raw19815step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19815step2 raw19815step2Labels permutation2 permutation7
    mixedMoment B raw19815step3 raw19815step3Labels = mixedMoment B raw19815step4 raw19815step4Labels := by
      have ha : raw19815step4 = raw19815step3 := by apply Matrix.ext; unfold raw19815step4 raw19815step3; decide +kernel
      have hl : raw19815step3Labels = labelEmbedding1 ∘ raw19815step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19815step3 raw19815step3Labels raw19815step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw19816 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19816step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19816step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19816step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19816step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19816step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19816step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19816step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19816step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19816 raw19816Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw19816 raw19816Labels = mixedMoment B raw19816step0 raw19816step0Labels := by
      have hz : ∀ j, raw19816 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19816step0 = (fun i j => raw19816 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19816step0 raw19816; decide +kernel
      have hl : raw19816step0Labels = raw19816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19816 raw19816Labels permutation520 hz
    mixedMoment B raw19816step0 raw19816step0Labels = mixedMoment B raw19816step1 raw19816step1Labels := by
      have hz : ∀ j, raw19816step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19816step1 = (fun i j => raw19816step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19816step1 raw19816step0; decide +kernel
      have hl : raw19816step1Labels = raw19816step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19816step0 raw19816step0Labels permutation104 hz
    mixedMoment B raw19816step1 raw19816step1Labels = mixedMoment B raw19816step2 raw19816step2Labels := by
      have hz : ∀ j, raw19816step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19816step2 = (fun i j => raw19816step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19816step2 raw19816step1; decide +kernel
      have hl : raw19816step2Labels = raw19816step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19816step1 raw19816step1Labels permutation14 hz
    mixedMoment B raw19816step2 raw19816step2Labels = mixedMoment B raw19816step3 raw19816step3Labels := by
      have ha : raw19816step3 = (fun i j => raw19816step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19816step3 raw19816step2; decide +kernel
      have hl : raw19816step3Labels = raw19816step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19816step2 raw19816step2Labels permutation2 permutation7
    mixedMoment B raw19816step3 raw19816step3Labels = mixedMoment B raw19816step4 raw19816step4Labels := by
      have ha : raw19816step4 = raw19816step3 := by apply Matrix.ext; unfold raw19816step4 raw19816step3; decide +kernel
      have hl : raw19816step3Labels = labelEmbedding1 ∘ raw19816step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19816step3 raw19816step3Labels raw19816step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw19817 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19817step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19817step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19817step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19817step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19817step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19817step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19817step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19817step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19817 raw19817Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw19817 raw19817Labels = mixedMoment B raw19817step0 raw19817step0Labels := by
      have hz : ∀ j, raw19817 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19817step0 = (fun i j => raw19817 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19817step0 raw19817; decide +kernel
      have hl : raw19817step0Labels = raw19817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19817 raw19817Labels permutation520 hz
    mixedMoment B raw19817step0 raw19817step0Labels = mixedMoment B raw19817step1 raw19817step1Labels := by
      have hz : ∀ j, raw19817step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19817step1 = (fun i j => raw19817step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19817step1 raw19817step0; decide +kernel
      have hl : raw19817step1Labels = raw19817step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19817step0 raw19817step0Labels permutation80 hz
    mixedMoment B raw19817step1 raw19817step1Labels = mixedMoment B raw19817step2 raw19817step2Labels := by
      have hz : ∀ j, raw19817step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19817step2 = (fun i j => raw19817step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19817step2 raw19817step1; decide +kernel
      have hl : raw19817step2Labels = raw19817step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19817step1 raw19817step1Labels permutation14 hz
    mixedMoment B raw19817step2 raw19817step2Labels = mixedMoment B raw19817step3 raw19817step3Labels := by
      have ha : raw19817step3 = (fun i j => raw19817step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19817step3 raw19817step2; decide +kernel
      have hl : raw19817step3Labels = raw19817step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19817step2 raw19817step2Labels permutation2 permutation7
    mixedMoment B raw19817step3 raw19817step3Labels = mixedMoment B raw19817step4 raw19817step4Labels := by
      have ha : raw19817step4 = raw19817step3 := by apply Matrix.ext; unfold raw19817step4 raw19817step3; decide +kernel
      have hl : raw19817step3Labels = labelEmbedding1 ∘ raw19817step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19817step3 raw19817step3Labels raw19817step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw19818 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19818step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19818step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, -2, 4]]
def raw19818step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19818step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 2, -4], ![-2, -2, 4]]
def raw19818step3Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19818step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw19818step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19818step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw19818step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19818 raw19818Labels = mixedMoment B node1313 node1313Labels := by
  calc
    mixedMoment B raw19818 raw19818Labels = mixedMoment B raw19818step0 raw19818step0Labels := by
      have hz : ∀ j, raw19818 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19818step0 = (fun i j => raw19818 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19818step0 raw19818; decide +kernel
      have hl : raw19818step0Labels = raw19818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19818 raw19818Labels permutation520 hz
    mixedMoment B raw19818step0 raw19818step0Labels = mixedMoment B raw19818step1 raw19818step1Labels := by
      have hz : ∀ j, raw19818step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19818step1 = (fun i j => raw19818step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19818step1 raw19818step0; decide +kernel
      have hl : raw19818step1Labels = raw19818step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19818step0 raw19818step0Labels permutation104 hz
    mixedMoment B raw19818step1 raw19818step1Labels = mixedMoment B raw19818step2 raw19818step2Labels := by
      have hz : ∀ j, raw19818step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19818step2 = (fun i j => raw19818step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19818step2 raw19818step1; decide +kernel
      have hl : raw19818step2Labels = raw19818step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19818step1 raw19818step1Labels permutation20 hz
    mixedMoment B raw19818step2 raw19818step2Labels = mixedMoment B raw19818step3 raw19818step3Labels := by
      have hz : ∀ j, raw19818step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19818step3 = (fun i j => raw19818step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19818step3 raw19818step2; decide +kernel
      have hl : raw19818step3Labels = raw19818step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19818step2 raw19818step2Labels permutation4 hz
    mixedMoment B raw19818step3 raw19818step3Labels = mixedMoment B raw19818step4 raw19818step4Labels := by
      have ha : raw19818step4 = (fun i j => raw19818step3 (permutation0 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19818step4 raw19818step3; decide +kernel
      have hl : raw19818step4Labels = raw19818step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19818step3 raw19818step3Labels permutation0 permutation7
    mixedMoment B raw19818step4 raw19818step4Labels = mixedMoment B raw19818step5 raw19818step5Labels := by
      have ha : raw19818step5 = raw19818step4 := by apply Matrix.ext; unfold raw19818step5 raw19818step4; decide +kernel
      have hl : raw19818step4Labels = labelEmbedding1 ∘ raw19818step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19818step4 raw19818step4Labels raw19818step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1313 node1313Labels := by rfl

def raw19819 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19819step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19819step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19819step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19819step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![4, -4, 0]]
def raw19819step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19819step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![4, -4, 0]]
def raw19819step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19819 raw19819Labels = mixedMoment B node1432 node1432Labels := by
  calc
    mixedMoment B raw19819 raw19819Labels = mixedMoment B raw19819step0 raw19819step0Labels := by
      have hz : ∀ j, raw19819 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19819step0 = (fun i j => raw19819 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19819step0 raw19819; decide +kernel
      have hl : raw19819step0Labels = raw19819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19819 raw19819Labels permutation434 hz
    mixedMoment B raw19819step0 raw19819step0Labels = mixedMoment B raw19819step1 raw19819step1Labels := by
      have hz : ∀ j, raw19819step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19819step1 = (fun i j => raw19819step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19819step1 raw19819step0; decide +kernel
      have hl : raw19819step1Labels = raw19819step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19819step0 raw19819step0Labels permutation80 hz
    mixedMoment B raw19819step1 raw19819step1Labels = mixedMoment B raw19819step2 raw19819step2Labels := by
      have hz : ∀ j, raw19819step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19819step2 = (fun i j => raw19819step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19819step2 raw19819step1; decide +kernel
      have hl : raw19819step2Labels = raw19819step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19819step1 raw19819step1Labels permutation14 hz
    mixedMoment B raw19819step2 raw19819step2Labels = mixedMoment B raw19819step3 raw19819step3Labels := by
      have ha : raw19819step3 = (fun i j => raw19819step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19819step3 raw19819step2; decide +kernel
      have hl : raw19819step3Labels = raw19819step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19819step2 raw19819step2Labels permutation2 permutation7
    mixedMoment B raw19819step3 raw19819step3Labels = mixedMoment B raw19819step4 raw19819step4Labels := by
      have ha : raw19819step4 = raw19819step3 := by apply Matrix.ext; unfold raw19819step4 raw19819step3; decide +kernel
      have hl : raw19819step3Labels = labelEmbedding1 ∘ raw19819step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19819step3 raw19819step3Labels raw19819step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1432 node1432Labels := by rfl

def raw19820 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19820step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19820step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19820step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw19820step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19820step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw19820step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19820 raw19820Labels = mixedMoment B node1255 node1255Labels := by
  calc
    mixedMoment B raw19820 raw19820Labels = mixedMoment B raw19820step0 raw19820step0Labels := by
      have hz : ∀ j, raw19820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19820step0 = (fun i j => raw19820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19820step0 raw19820; decide +kernel
      have hl : raw19820step0Labels = raw19820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19820 raw19820Labels permutation434 hz
    mixedMoment B raw19820step0 raw19820step0Labels = mixedMoment B raw19820step1 raw19820step1Labels := by
      have hz : ∀ j, raw19820step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19820step1 = (fun i j => raw19820step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19820step1 raw19820step0; decide +kernel
      have hl : raw19820step1Labels = raw19820step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19820step0 raw19820step0Labels permutation80 hz
    mixedMoment B raw19820step1 raw19820step1Labels = mixedMoment B raw19820step2 raw19820step2Labels := by
      have ha : raw19820step2 = (fun i j => raw19820step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19820step2 raw19820step1; decide +kernel
      have hl : raw19820step2Labels = raw19820step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19820step1 raw19820step1Labels permutation8 permutation7
    mixedMoment B raw19820step2 raw19820step2Labels = mixedMoment B raw19820step3 raw19820step3Labels := by
      have ha : raw19820step3 = raw19820step2 := by apply Matrix.ext; unfold raw19820step3 raw19820step2; decide +kernel
      have hl : raw19820step2Labels = labelEmbedding1 ∘ raw19820step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19820step2 raw19820step2Labels raw19820step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1255 node1255Labels := by rfl

def raw19821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19821step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19821step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw19821step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw19821step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19821 raw19821Labels = mixedMoment B node1255 node1255Labels := by
  calc
    mixedMoment B raw19821 raw19821Labels = mixedMoment B raw19821step0 raw19821step0Labels := by
      have hz : ∀ j, raw19821 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19821step0 = (fun i j => raw19821 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19821step0 raw19821; decide +kernel
      have hl : raw19821step0Labels = raw19821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19821 raw19821Labels permutation434 hz
    mixedMoment B raw19821step0 raw19821step0Labels = mixedMoment B raw19821step1 raw19821step1Labels := by
      have hz : ∀ j, raw19821step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19821step1 = (fun i j => raw19821step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19821step1 raw19821step0; decide +kernel
      have hl : raw19821step1Labels = raw19821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19821step0 raw19821step0Labels permutation56 hz
    mixedMoment B raw19821step1 raw19821step1Labels = mixedMoment B raw19821step2 raw19821step2Labels := by
      have ha : raw19821step2 = (fun i j => raw19821step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19821step2 raw19821step1; decide +kernel
      have hl : raw19821step2Labels = raw19821step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19821step1 raw19821step1Labels permutation8 permutation7
    mixedMoment B raw19821step2 raw19821step2Labels = mixedMoment B raw19821step3 raw19821step3Labels := by
      have ha : raw19821step3 = raw19821step2 := by apply Matrix.ext; unfold raw19821step3 raw19821step2; decide +kernel
      have hl : raw19821step2Labels = labelEmbedding1 ∘ raw19821step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19821step2 raw19821step2Labels raw19821step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1255 node1255Labels := by rfl

def raw19822 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19822step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19822step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19822step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19822step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw19822step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19822step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw19822step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19822 raw19822Labels = mixedMoment B node1255 node1255Labels := by
  calc
    mixedMoment B raw19822 raw19822Labels = mixedMoment B raw19822step0 raw19822step0Labels := by
      have hz : ∀ j, raw19822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19822step0 = (fun i j => raw19822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19822step0 raw19822; decide +kernel
      have hl : raw19822step0Labels = raw19822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19822 raw19822Labels permutation346 hz
    mixedMoment B raw19822step0 raw19822step0Labels = mixedMoment B raw19822step1 raw19822step1Labels := by
      have hz : ∀ j, raw19822step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19822step1 = (fun i j => raw19822step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19822step1 raw19822step0; decide +kernel
      have hl : raw19822step1Labels = raw19822step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19822step0 raw19822step0Labels permutation56 hz
    mixedMoment B raw19822step1 raw19822step1Labels = mixedMoment B raw19822step2 raw19822step2Labels := by
      have ha : raw19822step2 = (fun i j => raw19822step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19822step2 raw19822step1; decide +kernel
      have hl : raw19822step2Labels = raw19822step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19822step1 raw19822step1Labels permutation8 permutation7
    mixedMoment B raw19822step2 raw19822step2Labels = mixedMoment B raw19822step3 raw19822step3Labels := by
      have ha : raw19822step3 = raw19822step2 := by apply Matrix.ext; unfold raw19822step3 raw19822step2; decide +kernel
      have hl : raw19822step2Labels = labelEmbedding1 ∘ raw19822step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19822step2 raw19822step2Labels raw19822step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1255 node1255Labels := by rfl

def raw19823 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19823step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19823step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19823step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -4, 4]]
def raw19823step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19823step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def raw19823step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19823step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def raw19823step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19823 raw19823Labels = mixedMoment B node1285 node1285Labels := by
  calc
    mixedMoment B raw19823 raw19823Labels = mixedMoment B raw19823step0 raw19823step0Labels := by
      have hz : ∀ j, raw19823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19823step0 = (fun i j => raw19823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19823step0 raw19823; decide +kernel
      have hl : raw19823step0Labels = raw19823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19823 raw19823Labels permutation434 hz
    mixedMoment B raw19823step0 raw19823step0Labels = mixedMoment B raw19823step1 raw19823step1Labels := by
      have hz : ∀ j, raw19823step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19823step1 = (fun i j => raw19823step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19823step1 raw19823step0; decide +kernel
      have hl : raw19823step1Labels = raw19823step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19823step0 raw19823step0Labels permutation80 hz
    mixedMoment B raw19823step1 raw19823step1Labels = mixedMoment B raw19823step2 raw19823step2Labels := by
      have hz : ∀ j, raw19823step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19823step2 = (fun i j => raw19823step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19823step2 raw19823step1; decide +kernel
      have hl : raw19823step2Labels = raw19823step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19823step1 raw19823step1Labels permutation14 hz
    mixedMoment B raw19823step2 raw19823step2Labels = mixedMoment B raw19823step3 raw19823step3Labels := by
      have ha : raw19823step3 = (fun i j => raw19823step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19823step3 raw19823step2; decide +kernel
      have hl : raw19823step3Labels = raw19823step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19823step2 raw19823step2Labels permutation2 permutation7
    mixedMoment B raw19823step3 raw19823step3Labels = mixedMoment B raw19823step4 raw19823step4Labels := by
      have ha : raw19823step4 = raw19823step3 := by apply Matrix.ext; unfold raw19823step4 raw19823step3; decide +kernel
      have hl : raw19823step3Labels = labelEmbedding1 ∘ raw19823step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19823step3 raw19823step3Labels raw19823step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1285 node1285Labels := by rfl

def raw19824 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19824step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19824step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19824step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19824 raw19824Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19824 raw19824Labels = mixedMoment B raw19824step0 raw19824step0Labels := by
      have hz : ∀ j, raw19824 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19824step0 = (fun i j => raw19824 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19824step0 raw19824; decide +kernel
      have hl : raw19824step0Labels = raw19824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19824 raw19824Labels permutation434 hz
    mixedMoment B raw19824step0 raw19824step0Labels = mixedMoment B raw19824step1 raw19824step1Labels := by
      have hz : ∀ j, raw19824step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19824step1 = (fun i j => raw19824step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19824step1 raw19824step0; decide +kernel
      have hl : raw19824step1Labels = raw19824step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19824step0 raw19824step0Labels permutation80 hz
    mixedMoment B raw19824step1 raw19824step1Labels = mixedMoment B raw19824step2 raw19824step2Labels := by
      have hz : ∀ j, raw19824step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19824step2 = (fun i j => raw19824step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19824step2 raw19824step1; decide +kernel
      have hl : raw19824step2Labels = raw19824step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19824step1 raw19824step1Labels permutation14 hz
    mixedMoment B raw19824step2 raw19824step2Labels = mixedMoment B raw19824step3 raw19824step3Labels := by
      have ha : raw19824step3 = (fun i j => raw19824step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19824step3 raw19824step2; decide +kernel
      have hl : raw19824step3Labels = raw19824step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19824step2 raw19824step2Labels permutation7 permutation4
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw19825 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19825step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19825 raw19825Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw19825 raw19825Labels = mixedMoment B raw19825step0 raw19825step0Labels := by
      have hz : ∀ j, raw19825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19825step0 = (fun i j => raw19825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19825step0 raw19825; decide +kernel
      have hl : raw19825step0Labels = raw19825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19825 raw19825Labels permutation434 hz
    mixedMoment B raw19825step0 raw19825step0Labels = mixedMoment B raw19825step1 raw19825step1Labels := by
      have hz : ∀ j, raw19825step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19825step1 = (fun i j => raw19825step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19825step1 raw19825step0; decide +kernel
      have hl : raw19825step1Labels = raw19825step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19825step0 raw19825step0Labels permutation80 hz
    mixedMoment B raw19825step1 raw19825step1Labels = mixedMoment B raw19825step2 raw19825step2Labels := by
      have ha : raw19825step2 = (fun i j => raw19825step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19825step2 raw19825step1; decide +kernel
      have hl : raw19825step2Labels = raw19825step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19825step1 raw19825step1Labels permutation29 permutation4
    _ = mixedMoment B node1620 node1620Labels := by rfl

def raw19826 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19826 raw19826Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw19826 raw19826Labels = mixedMoment B raw19826step0 raw19826step0Labels := by
      have hz : ∀ j, raw19826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19826step0 = (fun i j => raw19826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19826step0 raw19826; decide +kernel
      have hl : raw19826step0Labels = raw19826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19826 raw19826Labels permutation434 hz
    mixedMoment B raw19826step0 raw19826step0Labels = mixedMoment B raw19826step1 raw19826step1Labels := by
      have hz : ∀ j, raw19826step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19826step1 = (fun i j => raw19826step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19826step1 raw19826step0; decide +kernel
      have hl : raw19826step1Labels = raw19826step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19826step0 raw19826step0Labels permutation56 hz
    mixedMoment B raw19826step1 raw19826step1Labels = mixedMoment B raw19826step2 raw19826step2Labels := by
      have ha : raw19826step2 = (fun i j => raw19826step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19826step2 raw19826step1; decide +kernel
      have hl : raw19826step2Labels = raw19826step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19826step1 raw19826step1Labels permutation29 permutation4
    _ = mixedMoment B node1620 node1620Labels := by rfl

def raw19827 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19827 raw19827Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw19827 raw19827Labels = mixedMoment B raw19827step0 raw19827step0Labels := by
      have hz : ∀ j, raw19827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19827step0 = (fun i j => raw19827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19827step0 raw19827; decide +kernel
      have hl : raw19827step0Labels = raw19827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19827 raw19827Labels permutation346 hz
    mixedMoment B raw19827step0 raw19827step0Labels = mixedMoment B raw19827step1 raw19827step1Labels := by
      have hz : ∀ j, raw19827step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19827step1 = (fun i j => raw19827step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19827step1 raw19827step0; decide +kernel
      have hl : raw19827step1Labels = raw19827step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19827step0 raw19827step0Labels permutation56 hz
    mixedMoment B raw19827step1 raw19827step1Labels = mixedMoment B raw19827step2 raw19827step2Labels := by
      have ha : raw19827step2 = (fun i j => raw19827step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19827step2 raw19827step1; decide +kernel
      have hl : raw19827step2Labels = raw19827step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19827step1 raw19827step1Labels permutation29 permutation4
    _ = mixedMoment B node1620 node1620Labels := by rfl

def raw19828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19828step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -3, 4]]
def raw19828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19828step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -3, 4]]
def raw19828step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19828step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def raw19828step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19828 raw19828Labels = mixedMoment B node1758 node1758Labels := by
  calc
    mixedMoment B raw19828 raw19828Labels = mixedMoment B raw19828step0 raw19828step0Labels := by
      have hz : ∀ j, raw19828 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19828step0 = (fun i j => raw19828 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19828step0 raw19828; decide +kernel
      have hl : raw19828step0Labels = raw19828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19828 raw19828Labels permutation520 hz
    mixedMoment B raw19828step0 raw19828step0Labels = mixedMoment B raw19828step1 raw19828step1Labels := by
      have hz : ∀ j, raw19828step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19828step1 = (fun i j => raw19828step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19828step1 raw19828step0; decide +kernel
      have hl : raw19828step1Labels = raw19828step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19828step0 raw19828step0Labels permutation104 hz
    mixedMoment B raw19828step1 raw19828step1Labels = mixedMoment B raw19828step2 raw19828step2Labels := by
      have hz : ∀ j, raw19828step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19828step2 = (fun i j => raw19828step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19828step2 raw19828step1; decide +kernel
      have hl : raw19828step2Labels = raw19828step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19828step1 raw19828step1Labels permutation20 hz
    mixedMoment B raw19828step2 raw19828step2Labels = mixedMoment B raw19828step3 raw19828step3Labels := by
      have hz : ∀ j, raw19828step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19828step3 = (fun i j => raw19828step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19828step3 raw19828step2; decide +kernel
      have hl : raw19828step3Labels = raw19828step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19828step2 raw19828step2Labels permutation4 hz
    mixedMoment B raw19828step3 raw19828step3Labels = mixedMoment B raw19828step4 raw19828step4Labels := by
      have ha : raw19828step4 = (fun i j => raw19828step3 (permutation1 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19828step4 raw19828step3; decide +kernel
      have hl : raw19828step4Labels = raw19828step3Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19828step3 raw19828step3Labels permutation1 permutation4
    _ = mixedMoment B node1758 node1758Labels := by rfl

def raw19829 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19829step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19829step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![3, 1, -4]]
def raw19829step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19829 raw19829Labels = mixedMoment B node855 node855Labels := by
  calc
    mixedMoment B raw19829 raw19829Labels = mixedMoment B raw19829step0 raw19829step0Labels := by
      have hz : ∀ j, raw19829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19829step0 = (fun i j => raw19829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19829step0 raw19829; decide +kernel
      have hl : raw19829step0Labels = raw19829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19829 raw19829Labels permutation434 hz
    mixedMoment B raw19829step0 raw19829step0Labels = mixedMoment B raw19829step1 raw19829step1Labels := by
      have hz : ∀ j, raw19829step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19829step1 = (fun i j => raw19829step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19829step1 raw19829step0; decide +kernel
      have hl : raw19829step1Labels = raw19829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19829step0 raw19829step0Labels permutation80 hz
    mixedMoment B raw19829step1 raw19829step1Labels = mixedMoment B raw19829step2 raw19829step2Labels := by
      have hz : ∀ j, raw19829step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19829step2 = (fun i j => raw19829step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19829step2 raw19829step1; decide +kernel
      have hl : raw19829step2Labels = raw19829step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19829step1 raw19829step1Labels permutation14 hz
    mixedMoment B raw19829step2 raw19829step2Labels = mixedMoment B raw19829step3 raw19829step3Labels := by
      have ha : raw19829step3 = (fun i j => raw19829step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19829step3 raw19829step2; decide +kernel
      have hl : raw19829step3Labels = raw19829step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19829step2 raw19829step2Labels permutation7 permutation4
    _ = mixedMoment B node855 node855Labels := by rfl

def raw19830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19830step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![4, 0, -4]]
def raw19830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19830step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-4, 2, 2]]
def raw19830step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19830step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw19830step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19830 raw19830Labels = mixedMoment B node832 node832Labels := by
  calc
    mixedMoment B raw19830 raw19830Labels = mixedMoment B raw19830step0 raw19830step0Labels := by
      have hz : ∀ j, raw19830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19830step0 = (fun i j => raw19830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19830step0 raw19830; decide +kernel
      have hl : raw19830step0Labels = raw19830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19830 raw19830Labels permutation434 hz
    mixedMoment B raw19830step0 raw19830step0Labels = mixedMoment B raw19830step1 raw19830step1Labels := by
      have hz : ∀ j, raw19830step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19830step1 = (fun i j => raw19830step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19830step1 raw19830step0; decide +kernel
      have hl : raw19830step1Labels = raw19830step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19830step0 raw19830step0Labels permutation80 hz
    mixedMoment B raw19830step1 raw19830step1Labels = mixedMoment B raw19830step2 raw19830step2Labels := by
      have hz : ∀ j, raw19830step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19830step2 = (fun i j => raw19830step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19830step2 raw19830step1; decide +kernel
      have hl : raw19830step2Labels = raw19830step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19830step1 raw19830step1Labels permutation14 hz
    mixedMoment B raw19830step2 raw19830step2Labels = mixedMoment B raw19830step3 raw19830step3Labels := by
      have ha : raw19830step3 = (fun i j => raw19830step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19830step3 raw19830step2; decide +kernel
      have hl : raw19830step3Labels = raw19830step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19830step2 raw19830step2Labels permutation7 permutation2
    mixedMoment B raw19830step3 raw19830step3Labels = mixedMoment B raw19830step4 raw19830step4Labels := by
      have ha : raw19830step4 = -raw19830step3 := by apply Matrix.ext; change ∀ i j, raw19830step4 i j = -(raw19830step3 i j); unfold raw19830step4 raw19830step3; decide +kernel
      have hl : raw19830step4Labels = raw19830step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node832 node832Labels := by rfl

def raw19831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19831step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw19831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19831step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw19831step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19831 raw19831Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw19831 raw19831Labels = mixedMoment B raw19831step0 raw19831step0Labels := by
      have hz : ∀ j, raw19831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19831step0 = (fun i j => raw19831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19831step0 raw19831; decide +kernel
      have hl : raw19831step0Labels = raw19831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19831 raw19831Labels permutation434 hz
    mixedMoment B raw19831step0 raw19831step0Labels = mixedMoment B raw19831step1 raw19831step1Labels := by
      have hz : ∀ j, raw19831step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19831step1 = (fun i j => raw19831step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19831step1 raw19831step0; decide +kernel
      have hl : raw19831step1Labels = raw19831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19831step0 raw19831step0Labels permutation80 hz
    mixedMoment B raw19831step1 raw19831step1Labels = mixedMoment B raw19831step2 raw19831step2Labels := by
      have ha : raw19831step2 = (fun i j => raw19831step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19831step2 raw19831step1; decide +kernel
      have hl : raw19831step2Labels = raw19831step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19831step1 raw19831step1Labels permutation31 permutation2
    mixedMoment B raw19831step2 raw19831step2Labels = mixedMoment B raw19831step3 raw19831step3Labels := by
      have ha : raw19831step3 = -raw19831step2 := by apply Matrix.ext; change ∀ i j, raw19831step3 i j = -(raw19831step2 i j); unfold raw19831step3 raw19831step2; decide +kernel
      have hl : raw19831step3Labels = raw19831step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node826 node826Labels := by rfl

def raw19832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19832step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw19832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19832step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw19832step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19832 raw19832Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw19832 raw19832Labels = mixedMoment B raw19832step0 raw19832step0Labels := by
      have hz : ∀ j, raw19832 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19832step0 = (fun i j => raw19832 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19832step0 raw19832; decide +kernel
      have hl : raw19832step0Labels = raw19832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19832 raw19832Labels permutation434 hz
    mixedMoment B raw19832step0 raw19832step0Labels = mixedMoment B raw19832step1 raw19832step1Labels := by
      have hz : ∀ j, raw19832step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19832step1 = (fun i j => raw19832step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19832step1 raw19832step0; decide +kernel
      have hl : raw19832step1Labels = raw19832step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19832step0 raw19832step0Labels permutation56 hz
    mixedMoment B raw19832step1 raw19832step1Labels = mixedMoment B raw19832step2 raw19832step2Labels := by
      have ha : raw19832step2 = (fun i j => raw19832step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19832step2 raw19832step1; decide +kernel
      have hl : raw19832step2Labels = raw19832step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19832step1 raw19832step1Labels permutation31 permutation2
    mixedMoment B raw19832step2 raw19832step2Labels = mixedMoment B raw19832step3 raw19832step3Labels := by
      have ha : raw19832step3 = -raw19832step2 := by apply Matrix.ext; change ∀ i j, raw19832step3 i j = -(raw19832step2 i j); unfold raw19832step3 raw19832step2; decide +kernel
      have hl : raw19832step3Labels = raw19832step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node826 node826Labels := by rfl

def raw19833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![4, 0, -4]]
def raw19833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw19833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19833step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw19833step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19833 raw19833Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw19833 raw19833Labels = mixedMoment B raw19833step0 raw19833step0Labels := by
      have hz : ∀ j, raw19833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19833step0 = (fun i j => raw19833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19833step0 raw19833; decide +kernel
      have hl : raw19833step0Labels = raw19833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19833 raw19833Labels permutation346 hz
    mixedMoment B raw19833step0 raw19833step0Labels = mixedMoment B raw19833step1 raw19833step1Labels := by
      have hz : ∀ j, raw19833step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19833step1 = (fun i j => raw19833step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19833step1 raw19833step0; decide +kernel
      have hl : raw19833step1Labels = raw19833step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19833step0 raw19833step0Labels permutation56 hz
    mixedMoment B raw19833step1 raw19833step1Labels = mixedMoment B raw19833step2 raw19833step2Labels := by
      have ha : raw19833step2 = (fun i j => raw19833step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19833step2 raw19833step1; decide +kernel
      have hl : raw19833step2Labels = raw19833step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19833step1 raw19833step1Labels permutation31 permutation2
    mixedMoment B raw19833step2 raw19833step2Labels = mixedMoment B raw19833step3 raw19833step3Labels := by
      have ha : raw19833step3 = -raw19833step2 := by apply Matrix.ext; change ∀ i j, raw19833step3 i j = -(raw19833step2 i j); unfold raw19833step3 raw19833step2; decide +kernel
      have hl : raw19833step3Labels = raw19833step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node826 node826Labels := by rfl

def raw19834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19834step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![4, 0, -4]]
def raw19834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19834step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -1, 2], ![-3, 1, 2]]
def raw19834step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19834step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw19834step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19834 raw19834Labels = mixedMoment B node859 node859Labels := by
  calc
    mixedMoment B raw19834 raw19834Labels = mixedMoment B raw19834step0 raw19834step0Labels := by
      have hz : ∀ j, raw19834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19834step0 = (fun i j => raw19834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19834step0 raw19834; decide +kernel
      have hl : raw19834step0Labels = raw19834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19834 raw19834Labels permutation434 hz
    mixedMoment B raw19834step0 raw19834step0Labels = mixedMoment B raw19834step1 raw19834step1Labels := by
      have hz : ∀ j, raw19834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19834step1 = (fun i j => raw19834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19834step1 raw19834step0; decide +kernel
      have hl : raw19834step1Labels = raw19834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19834step0 raw19834step0Labels permutation80 hz
    mixedMoment B raw19834step1 raw19834step1Labels = mixedMoment B raw19834step2 raw19834step2Labels := by
      have hz : ∀ j, raw19834step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19834step2 = (fun i j => raw19834step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19834step2 raw19834step1; decide +kernel
      have hl : raw19834step2Labels = raw19834step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19834step1 raw19834step1Labels permutation14 hz
    mixedMoment B raw19834step2 raw19834step2Labels = mixedMoment B raw19834step3 raw19834step3Labels := by
      have ha : raw19834step3 = (fun i j => raw19834step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19834step3 raw19834step2; decide +kernel
      have hl : raw19834step3Labels = raw19834step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19834step2 raw19834step2Labels permutation7 permutation2
    mixedMoment B raw19834step3 raw19834step3Labels = mixedMoment B raw19834step4 raw19834step4Labels := by
      have ha : raw19834step4 = -raw19834step3 := by apply Matrix.ext; change ∀ i j, raw19834step4 i j = -(raw19834step3 i j); unfold raw19834step4 raw19834step3; decide +kernel
      have hl : raw19834step4Labels = raw19834step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node859 node859Labels := by rfl

def raw19835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19835step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![3, 1, -4]]
def raw19835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19835step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw19835step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19835step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw19835step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19835 raw19835Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw19835 raw19835Labels = mixedMoment B raw19835step0 raw19835step0Labels := by
      have hz : ∀ j, raw19835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19835step0 = (fun i j => raw19835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19835step0 raw19835; decide +kernel
      have hl : raw19835step0Labels = raw19835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19835 raw19835Labels permutation434 hz
    mixedMoment B raw19835step0 raw19835step0Labels = mixedMoment B raw19835step1 raw19835step1Labels := by
      have hz : ∀ j, raw19835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19835step1 = (fun i j => raw19835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19835step1 raw19835step0; decide +kernel
      have hl : raw19835step1Labels = raw19835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19835step0 raw19835step0Labels permutation80 hz
    mixedMoment B raw19835step1 raw19835step1Labels = mixedMoment B raw19835step2 raw19835step2Labels := by
      have hz : ∀ j, raw19835step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19835step2 = (fun i j => raw19835step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19835step2 raw19835step1; decide +kernel
      have hl : raw19835step2Labels = raw19835step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19835step1 raw19835step1Labels permutation14 hz
    mixedMoment B raw19835step2 raw19835step2Labels = mixedMoment B raw19835step3 raw19835step3Labels := by
      have ha : raw19835step3 = (fun i j => raw19835step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19835step3 raw19835step2; decide +kernel
      have hl : raw19835step3Labels = raw19835step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19835step2 raw19835step2Labels permutation7 permutation2
    mixedMoment B raw19835step3 raw19835step3Labels = mixedMoment B raw19835step4 raw19835step4Labels := by
      have ha : raw19835step4 = -raw19835step3 := by apply Matrix.ext; change ∀ i j, raw19835step4 i j = -(raw19835step3 i j); unfold raw19835step4 raw19835step3; decide +kernel
      have hl : raw19835step4Labels = raw19835step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1741 node1741Labels := by rfl

def raw19836 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![-2, 2], ![4, -4]]
def raw19836Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19836step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![4, -4]]
def raw19836step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19836step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![4, -4]]
def raw19836step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19836step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![4, -4]]
def raw19836step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19836step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-2, 2], ![-2, 2]]
def raw19836step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19836step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw19836step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19836 raw19836Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw19836 raw19836Labels = mixedMoment B raw19836step0 raw19836step0Labels := by
      have hz : ∀ j, raw19836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19836step0 = (fun i j => raw19836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19836step0 raw19836; decide +kernel
      have hl : raw19836step0Labels = raw19836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19836 raw19836Labels permutation434 hz
    mixedMoment B raw19836step0 raw19836step0Labels = mixedMoment B raw19836step1 raw19836step1Labels := by
      have hz : ∀ j, raw19836step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19836step1 = (fun i j => raw19836step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19836step1 raw19836step0; decide +kernel
      have hl : raw19836step1Labels = raw19836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19836step0 raw19836step0Labels permutation80 hz
    mixedMoment B raw19836step1 raw19836step1Labels = mixedMoment B raw19836step2 raw19836step2Labels := by
      have hz : ∀ j, raw19836step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19836step2 = (fun i j => raw19836step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19836step2 raw19836step1; decide +kernel
      have hl : raw19836step2Labels = raw19836step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19836step1 raw19836step1Labels permutation14 hz
    mixedMoment B raw19836step2 raw19836step2Labels = mixedMoment B raw19836step3 raw19836step3Labels := by
      have ha : raw19836step3 = (fun i j => raw19836step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19836step3 raw19836step2; decide +kernel
      have hl : raw19836step3Labels = raw19836step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19836step2 raw19836step2Labels permutation6 permutation0
    mixedMoment B raw19836step3 raw19836step3Labels = mixedMoment B raw19836step4 raw19836step4Labels := by
      have ha : raw19836step4 = -raw19836step3 := by apply Matrix.ext; change ∀ i j, raw19836step4 i j = -(raw19836step3 i j); unfold raw19836step4 raw19836step3; decide +kernel
      have hl : raw19836step4Labels = raw19836step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4071 node4071Labels := by rfl

def raw19837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw19837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19837step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw19837step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19837 raw19837Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw19837 raw19837Labels = mixedMoment B raw19837step0 raw19837step0Labels := by
      have hz : ∀ j, raw19837 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19837step0 = (fun i j => raw19837 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19837step0 raw19837; decide +kernel
      have hl : raw19837step0Labels = raw19837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19837 raw19837Labels permutation434 hz
    mixedMoment B raw19837step0 raw19837step0Labels = mixedMoment B raw19837step1 raw19837step1Labels := by
      have hz : ∀ j, raw19837step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19837step1 = (fun i j => raw19837step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19837step1 raw19837step0; decide +kernel
      have hl : raw19837step1Labels = raw19837step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19837step0 raw19837step0Labels permutation80 hz
    mixedMoment B raw19837step1 raw19837step1Labels = mixedMoment B raw19837step2 raw19837step2Labels := by
      have ha : raw19837step2 = (fun i j => raw19837step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19837step2 raw19837step1; decide +kernel
      have hl : raw19837step2Labels = raw19837step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19837step1 raw19837step1Labels permutation29 permutation2
    mixedMoment B raw19837step2 raw19837step2Labels = mixedMoment B raw19837step3 raw19837step3Labels := by
      have ha : raw19837step3 = -raw19837step2 := by apply Matrix.ext; change ∀ i j, raw19837step3 i j = -(raw19837step2 i j); unfold raw19837step3 raw19837step2; decide +kernel
      have hl : raw19837step3Labels = raw19837step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node726 node726Labels := by rfl

def raw19838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw19838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw19838step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19838 raw19838Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw19838 raw19838Labels = mixedMoment B raw19838step0 raw19838step0Labels := by
      have hz : ∀ j, raw19838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19838step0 = (fun i j => raw19838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19838step0 raw19838; decide +kernel
      have hl : raw19838step0Labels = raw19838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19838 raw19838Labels permutation434 hz
    mixedMoment B raw19838step0 raw19838step0Labels = mixedMoment B raw19838step1 raw19838step1Labels := by
      have hz : ∀ j, raw19838step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19838step1 = (fun i j => raw19838step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19838step1 raw19838step0; decide +kernel
      have hl : raw19838step1Labels = raw19838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19838step0 raw19838step0Labels permutation56 hz
    mixedMoment B raw19838step1 raw19838step1Labels = mixedMoment B raw19838step2 raw19838step2Labels := by
      have ha : raw19838step2 = (fun i j => raw19838step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19838step2 raw19838step1; decide +kernel
      have hl : raw19838step2Labels = raw19838step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19838step1 raw19838step1Labels permutation29 permutation2
    mixedMoment B raw19838step2 raw19838step2Labels = mixedMoment B raw19838step3 raw19838step3Labels := by
      have ha : raw19838step3 = -raw19838step2 := by apply Matrix.ext; change ∀ i j, raw19838step3 i j = -(raw19838step2 i j); unfold raw19838step3 raw19838step2; decide +kernel
      have hl : raw19838step3Labels = raw19838step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node726 node726Labels := by rfl

def raw19839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![4, 0, -4]]
def raw19839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw19839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19839step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw19839step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19839 raw19839Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw19839 raw19839Labels = mixedMoment B raw19839step0 raw19839step0Labels := by
      have hz : ∀ j, raw19839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19839step0 = (fun i j => raw19839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19839step0 raw19839; decide +kernel
      have hl : raw19839step0Labels = raw19839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19839 raw19839Labels permutation346 hz
    mixedMoment B raw19839step0 raw19839step0Labels = mixedMoment B raw19839step1 raw19839step1Labels := by
      have hz : ∀ j, raw19839step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19839step1 = (fun i j => raw19839step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19839step1 raw19839step0; decide +kernel
      have hl : raw19839step1Labels = raw19839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19839step0 raw19839step0Labels permutation56 hz
    mixedMoment B raw19839step1 raw19839step1Labels = mixedMoment B raw19839step2 raw19839step2Labels := by
      have ha : raw19839step2 = (fun i j => raw19839step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19839step2 raw19839step1; decide +kernel
      have hl : raw19839step2Labels = raw19839step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19839step1 raw19839step1Labels permutation29 permutation2
    mixedMoment B raw19839step2 raw19839step2Labels = mixedMoment B raw19839step3 raw19839step3Labels := by
      have ha : raw19839step3 = -raw19839step2 := by apply Matrix.ext; change ∀ i j, raw19839step3 i j = -(raw19839step2 i j); unfold raw19839step3 raw19839step2; decide +kernel
      have hl : raw19839step3Labels = raw19839step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node726 node726Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
