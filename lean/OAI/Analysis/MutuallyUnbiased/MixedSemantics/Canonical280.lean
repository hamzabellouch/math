import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
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

def raw35840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw35840step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35840step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35840step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35840step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35840 raw35840Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw35840 raw35840Labels = mixedMoment B raw35840step0 raw35840step0Labels := by
      have hz : ∀ j, raw35840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35840step0 = (fun i j => raw35840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35840step0 raw35840; decide +kernel
      have hl : raw35840step0Labels = raw35840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35840 raw35840Labels permutation434 hz
    mixedMoment B raw35840step0 raw35840step0Labels = mixedMoment B raw35840step1 raw35840step1Labels := by
      have ha : raw35840step1 = (fun i j => raw35840step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35840step1 raw35840step0; decide +kernel
      have hl : raw35840step1Labels = raw35840step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35840step0 raw35840step0Labels permutation150 permutation3
    mixedMoment B raw35840step1 raw35840step1Labels = mixedMoment B raw35840step2 raw35840step2Labels := by
      have ha : raw35840step2 = -raw35840step1 := by apply Matrix.ext; change ∀ i j, raw35840step2 i j = -(raw35840step1 i j); unfold raw35840step2 raw35840step1; decide +kernel
      have hl : raw35840step2Labels = raw35840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35840step2 raw35840step2Labels = mixedMoment B raw35840step3 raw35840step3Labels := by
      have ha : raw35840step3 = raw35840step2 := by apply Matrix.ext; unfold raw35840step3 raw35840step2; decide +kernel
      have hl : raw35840step2Labels = labelEmbedding6 ∘ raw35840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35840step2 raw35840step2Labels raw35840step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw35841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw35841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35841step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35841 raw35841Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw35841 raw35841Labels = mixedMoment B raw35841step0 raw35841step0Labels := by
      have ha : raw35841step0 = (fun i j => raw35841 (permutation649 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35841step0 raw35841; decide +kernel
      have hl : raw35841step0Labels = raw35841Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35841 raw35841Labels permutation649 permutation5
    mixedMoment B raw35841step0 raw35841step0Labels = mixedMoment B raw35841step1 raw35841step1Labels := by
      have ha : raw35841step1 = raw35841step0 := by apply Matrix.ext; unfold raw35841step1 raw35841step0; decide +kernel
      have hl : raw35841step0Labels = labelEmbedding8 ∘ raw35841step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35841step0 raw35841step0Labels raw35841step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw35842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw35842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35842step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw35842step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35842step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw35842step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35842 raw35842Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw35842 raw35842Labels = mixedMoment B raw35842step0 raw35842step0Labels := by
      have ha : raw35842step0 = (fun i j => raw35842 (permutation299 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35842step0 raw35842; decide +kernel
      have hl : raw35842step0Labels = raw35842Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35842 raw35842Labels permutation299 permutation5
    mixedMoment B raw35842step0 raw35842step0Labels = mixedMoment B raw35842step1 raw35842step1Labels := by
      have ha : raw35842step1 = -raw35842step0 := by apply Matrix.ext; change ∀ i j, raw35842step1 i j = -(raw35842step0 i j); unfold raw35842step1 raw35842step0; decide +kernel
      have hl : raw35842step1Labels = raw35842step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35842step1 raw35842step1Labels = mixedMoment B raw35842step2 raw35842step2Labels := by
      have ha : raw35842step2 = raw35842step1 := by apply Matrix.ext; unfold raw35842step2 raw35842step1; decide +kernel
      have hl : raw35842step1Labels = labelEmbedding8 ∘ raw35842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35842step1 raw35842step1Labels raw35842step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw35843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35843step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35843step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35843 raw35843Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw35843 raw35843Labels = mixedMoment B raw35843step0 raw35843step0Labels := by
      have ha : raw35843step0 = (fun i j => raw35843 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35843step0 raw35843; decide +kernel
      have hl : raw35843step0Labels = raw35843Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35843 raw35843Labels permutation267 permutation3
    mixedMoment B raw35843step0 raw35843step0Labels = mixedMoment B raw35843step1 raw35843step1Labels := by
      have ha : raw35843step1 = raw35843step0 := by apply Matrix.ext; unfold raw35843step1 raw35843step0; decide +kernel
      have hl : raw35843step0Labels = labelEmbedding6 ∘ raw35843step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35843step0 raw35843step0Labels raw35843step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

def raw35844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35844step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35844step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35844 raw35844Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw35844 raw35844Labels = mixedMoment B raw35844step0 raw35844step0Labels := by
      have hz : ∀ j, raw35844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35844step0 = (fun i j => raw35844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35844step0 raw35844; decide +kernel
      have hl : raw35844step0Labels = raw35844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35844 raw35844Labels permutation434 hz
    mixedMoment B raw35844step0 raw35844step0Labels = mixedMoment B raw35844step1 raw35844step1Labels := by
      have ha : raw35844step1 = (fun i j => raw35844step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35844step1 raw35844step0; decide +kernel
      have hl : raw35844step1Labels = raw35844step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35844step0 raw35844step0Labels permutation56 permutation3
    mixedMoment B raw35844step1 raw35844step1Labels = mixedMoment B raw35844step2 raw35844step2Labels := by
      have ha : raw35844step2 = raw35844step1 := by apply Matrix.ext; unfold raw35844step2 raw35844step1; decide +kernel
      have hl : raw35844step1Labels = labelEmbedding6 ∘ raw35844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35844step1 raw35844step1Labels raw35844step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw35845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw35845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35845step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35845 raw35845Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw35845 raw35845Labels = mixedMoment B raw35845step0 raw35845step0Labels := by
      have ha : raw35845step0 = (fun i j => raw35845 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35845step0 raw35845; decide +kernel
      have hl : raw35845step0Labels = raw35845Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35845 raw35845Labels permutation277 permutation3
    mixedMoment B raw35845step0 raw35845step0Labels = mixedMoment B raw35845step1 raw35845step1Labels := by
      have ha : raw35845step1 = raw35845step0 := by apply Matrix.ext; unfold raw35845step1 raw35845step0; decide +kernel
      have hl : raw35845step0Labels = labelEmbedding6 ∘ raw35845step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35845step0 raw35845step0Labels raw35845step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw35846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw35846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35846 raw35846Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw35846 raw35846Labels = mixedMoment B raw35846step0 raw35846step0Labels := by
      have ha : raw35846step0 = (fun i j => raw35846 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35846step0 raw35846; decide +kernel
      have hl : raw35846step0Labels = raw35846Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35846 raw35846Labels permutation162 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

def raw35847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35847step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw35847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35847 raw35847Labels = mixedMoment B node4659 node4659Labels := by
  calc
    mixedMoment B raw35847 raw35847Labels = mixedMoment B raw35847step0 raw35847step0Labels := by
      have ha : raw35847step0 = (fun i j => raw35847 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35847step0 raw35847; decide +kernel
      have hl : raw35847step0Labels = raw35847Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35847 raw35847Labels permutation267 permutation3
    mixedMoment B raw35847step0 raw35847step0Labels = mixedMoment B raw35847step1 raw35847step1Labels := by
      have ha : raw35847step1 = raw35847step0 := by apply Matrix.ext; unfold raw35847step1 raw35847step0; decide +kernel
      have hl : raw35847step0Labels = labelEmbedding6 ∘ raw35847step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35847step0 raw35847step0Labels raw35847step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4659 node4659Labels := by rfl

def raw35848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35848step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35848step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35848step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35848 raw35848Labels = mixedMoment B node5315 node5315Labels := by
  calc
    mixedMoment B raw35848 raw35848Labels = mixedMoment B raw35848step0 raw35848step0Labels := by
      have ha : raw35848step0 = (fun i j => raw35848 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35848step0 raw35848; decide +kernel
      have hl : raw35848step0Labels = raw35848Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35848 raw35848Labels permutation518 permutation3
    mixedMoment B raw35848step0 raw35848step0Labels = mixedMoment B raw35848step1 raw35848step1Labels := by
      have ha : raw35848step1 = -raw35848step0 := by apply Matrix.ext; change ∀ i j, raw35848step1 i j = -(raw35848step0 i j); unfold raw35848step1 raw35848step0; decide +kernel
      have hl : raw35848step1Labels = raw35848step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35848step1 raw35848step1Labels = mixedMoment B raw35848step2 raw35848step2Labels := by
      have ha : raw35848step2 = raw35848step1 := by apply Matrix.ext; unfold raw35848step2 raw35848step1; decide +kernel
      have hl : raw35848step1Labels = labelEmbedding6 ∘ raw35848step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35848step1 raw35848step1Labels raw35848step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5315 node5315Labels := by rfl

def raw35849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw35849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35849step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35849step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35849step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35849 raw35849Labels = mixedMoment B node5320 node5320Labels := by
  calc
    mixedMoment B raw35849 raw35849Labels = mixedMoment B raw35849step0 raw35849step0Labels := by
      have ha : raw35849step0 = (fun i j => raw35849 (permutation512 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35849step0 raw35849; decide +kernel
      have hl : raw35849step0Labels = raw35849Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35849 raw35849Labels permutation512 permutation3
    mixedMoment B raw35849step0 raw35849step0Labels = mixedMoment B raw35849step1 raw35849step1Labels := by
      have ha : raw35849step1 = -raw35849step0 := by apply Matrix.ext; change ∀ i j, raw35849step1 i j = -(raw35849step0 i j); unfold raw35849step1 raw35849step0; decide +kernel
      have hl : raw35849step1Labels = raw35849step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35849step1 raw35849step1Labels = mixedMoment B raw35849step2 raw35849step2Labels := by
      have ha : raw35849step2 = raw35849step1 := by apply Matrix.ext; unfold raw35849step2 raw35849step1; decide +kernel
      have hl : raw35849step1Labels = labelEmbedding6 ∘ raw35849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35849step1 raw35849step1Labels raw35849step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5320 node5320Labels := by rfl

def raw35850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw35850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35850step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35850 raw35850Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw35850 raw35850Labels = mixedMoment B raw35850step0 raw35850step0Labels := by
      have ha : raw35850step0 = (fun i j => raw35850 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35850step0 raw35850; decide +kernel
      have hl : raw35850step0Labels = raw35850Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35850 raw35850Labels permutation268 permutation3
    mixedMoment B raw35850step0 raw35850step0Labels = mixedMoment B raw35850step1 raw35850step1Labels := by
      have ha : raw35850step1 = raw35850step0 := by apply Matrix.ext; unfold raw35850step1 raw35850step0; decide +kernel
      have hl : raw35850step0Labels = labelEmbedding6 ∘ raw35850step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35850step0 raw35850step0Labels raw35850step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw35851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw35851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35851step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35851 raw35851Labels = mixedMoment B node4661 node4661Labels := by
  calc
    mixedMoment B raw35851 raw35851Labels = mixedMoment B raw35851step0 raw35851step0Labels := by
      have ha : raw35851step0 = (fun i j => raw35851 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35851step0 raw35851; decide +kernel
      have hl : raw35851step0Labels = raw35851Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35851 raw35851Labels permutation265 permutation3
    mixedMoment B raw35851step0 raw35851step0Labels = mixedMoment B raw35851step1 raw35851step1Labels := by
      have ha : raw35851step1 = raw35851step0 := by apply Matrix.ext; unfold raw35851step1 raw35851step0; decide +kernel
      have hl : raw35851step0Labels = labelEmbedding6 ∘ raw35851step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35851step0 raw35851step0Labels raw35851step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4661 node4661Labels := by rfl

def raw35852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw35852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35852step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35852step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35852step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35852 raw35852Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw35852 raw35852Labels = mixedMoment B raw35852step0 raw35852step0Labels := by
      have ha : raw35852step0 = (fun i j => raw35852 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35852step0 raw35852; decide +kernel
      have hl : raw35852step0Labels = raw35852Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35852 raw35852Labels permutation687 permutation3
    mixedMoment B raw35852step0 raw35852step0Labels = mixedMoment B raw35852step1 raw35852step1Labels := by
      have ha : raw35852step1 = -raw35852step0 := by apply Matrix.ext; change ∀ i j, raw35852step1 i j = -(raw35852step0 i j); unfold raw35852step1 raw35852step0; decide +kernel
      have hl : raw35852step1Labels = raw35852step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35852step1 raw35852step1Labels = mixedMoment B raw35852step2 raw35852step2Labels := by
      have ha : raw35852step2 = raw35852step1 := by apply Matrix.ext; unfold raw35852step2 raw35852step1; decide +kernel
      have hl : raw35852step1Labels = labelEmbedding6 ∘ raw35852step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35852step1 raw35852step1Labels raw35852step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

def raw35853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw35853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw35853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35853step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35853step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35853step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35853step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35853 raw35853Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35853 raw35853Labels = mixedMoment B raw35853step0 raw35853step0Labels := by
      have hz : ∀ j, raw35853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35853step0 = (fun i j => raw35853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35853step0 raw35853; decide +kernel
      have hl : raw35853step0Labels = raw35853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35853 raw35853Labels permutation434 hz
    mixedMoment B raw35853step0 raw35853step0Labels = mixedMoment B raw35853step1 raw35853step1Labels := by
      have ha : raw35853step1 = (fun i j => raw35853step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35853step1 raw35853step0; decide +kernel
      have hl : raw35853step1Labels = raw35853step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35853step0 raw35853step0Labels permutation150 permutation3
    mixedMoment B raw35853step1 raw35853step1Labels = mixedMoment B raw35853step2 raw35853step2Labels := by
      have ha : raw35853step2 = -raw35853step1 := by apply Matrix.ext; change ∀ i j, raw35853step2 i j = -(raw35853step1 i j); unfold raw35853step2 raw35853step1; decide +kernel
      have hl : raw35853step2Labels = raw35853step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35853step2 raw35853step2Labels = mixedMoment B raw35853step3 raw35853step3Labels := by
      have ha : raw35853step3 = raw35853step2 := by apply Matrix.ext; unfold raw35853step3 raw35853step2; decide +kernel
      have hl : raw35853step2Labels = labelEmbedding6 ∘ raw35853step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35853step2 raw35853step2Labels raw35853step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw35854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw35854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35854step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35854 raw35854Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw35854 raw35854Labels = mixedMoment B raw35854step0 raw35854step0Labels := by
      have ha : raw35854step0 = (fun i j => raw35854 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35854step0 raw35854; decide +kernel
      have hl : raw35854step0Labels = raw35854Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35854 raw35854Labels permutation266 permutation3
    mixedMoment B raw35854step0 raw35854step0Labels = mixedMoment B raw35854step1 raw35854step1Labels := by
      have ha : raw35854step1 = raw35854step0 := by apply Matrix.ext; unfold raw35854step1 raw35854step0; decide +kernel
      have hl : raw35854step0Labels = labelEmbedding6 ∘ raw35854step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35854step0 raw35854step0Labels raw35854step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw35855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw35855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw35855step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw35855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35855 raw35855Labels = mixedMoment B node4658 node4658Labels := by
  calc
    mixedMoment B raw35855 raw35855Labels = mixedMoment B raw35855step0 raw35855step0Labels := by
      have ha : raw35855step0 = (fun i j => raw35855 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35855step0 raw35855; decide +kernel
      have hl : raw35855step0Labels = raw35855Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35855 raw35855Labels permutation267 permutation3
    mixedMoment B raw35855step0 raw35855step0Labels = mixedMoment B raw35855step1 raw35855step1Labels := by
      have ha : raw35855step1 = raw35855step0 := by apply Matrix.ext; unfold raw35855step1 raw35855step0; decide +kernel
      have hl : raw35855step0Labels = labelEmbedding6 ∘ raw35855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35855step0 raw35855step0Labels raw35855step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4658 node4658Labels := by rfl

def raw35856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw35856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35856step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35856step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35856step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35856 raw35856Labels = mixedMoment B node4716 node4716Labels := by
  calc
    mixedMoment B raw35856 raw35856Labels = mixedMoment B raw35856step0 raw35856step0Labels := by
      have ha : raw35856step0 = (fun i j => raw35856 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35856step0 raw35856; decide +kernel
      have hl : raw35856step0Labels = raw35856Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35856 raw35856Labels permutation663 permutation3
    mixedMoment B raw35856step0 raw35856step0Labels = mixedMoment B raw35856step1 raw35856step1Labels := by
      have ha : raw35856step1 = -raw35856step0 := by apply Matrix.ext; change ∀ i j, raw35856step1 i j = -(raw35856step0 i j); unfold raw35856step1 raw35856step0; decide +kernel
      have hl : raw35856step1Labels = raw35856step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35856step1 raw35856step1Labels = mixedMoment B raw35856step2 raw35856step2Labels := by
      have ha : raw35856step2 = raw35856step1 := by apply Matrix.ext; unfold raw35856step2 raw35856step1; decide +kernel
      have hl : raw35856step1Labels = labelEmbedding6 ∘ raw35856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35856step1 raw35856step1Labels raw35856step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4716 node4716Labels := by rfl

def raw35857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw35857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw35857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35857step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35857step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35857step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35857step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35857 raw35857Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw35857 raw35857Labels = mixedMoment B raw35857step0 raw35857step0Labels := by
      have hz : ∀ j, raw35857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35857step0 = (fun i j => raw35857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35857step0 raw35857; decide +kernel
      have hl : raw35857step0Labels = raw35857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35857 raw35857Labels permutation434 hz
    mixedMoment B raw35857step0 raw35857step0Labels = mixedMoment B raw35857step1 raw35857step1Labels := by
      have ha : raw35857step1 = (fun i j => raw35857step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35857step1 raw35857step0; decide +kernel
      have hl : raw35857step1Labels = raw35857step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35857step0 raw35857step0Labels permutation150 permutation3
    mixedMoment B raw35857step1 raw35857step1Labels = mixedMoment B raw35857step2 raw35857step2Labels := by
      have ha : raw35857step2 = -raw35857step1 := by apply Matrix.ext; change ∀ i j, raw35857step2 i j = -(raw35857step1 i j); unfold raw35857step2 raw35857step1; decide +kernel
      have hl : raw35857step2Labels = raw35857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35857step2 raw35857step2Labels = mixedMoment B raw35857step3 raw35857step3Labels := by
      have ha : raw35857step3 = raw35857step2 := by apply Matrix.ext; unfold raw35857step3 raw35857step2; decide +kernel
      have hl : raw35857step2Labels = labelEmbedding6 ∘ raw35857step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35857step2 raw35857step2Labels raw35857step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw35858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw35858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35858step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35858step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35858step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35858 raw35858Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw35858 raw35858Labels = mixedMoment B raw35858step0 raw35858step0Labels := by
      have ha : raw35858step0 = (fun i j => raw35858 (permutation657 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35858step0 raw35858; decide +kernel
      have hl : raw35858step0Labels = raw35858Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35858 raw35858Labels permutation657 permutation3
    mixedMoment B raw35858step0 raw35858step0Labels = mixedMoment B raw35858step1 raw35858step1Labels := by
      have ha : raw35858step1 = -raw35858step0 := by apply Matrix.ext; change ∀ i j, raw35858step1 i j = -(raw35858step0 i j); unfold raw35858step1 raw35858step0; decide +kernel
      have hl : raw35858step1Labels = raw35858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35858step1 raw35858step1Labels = mixedMoment B raw35858step2 raw35858step2Labels := by
      have ha : raw35858step2 = raw35858step1 := by apply Matrix.ext; unfold raw35858step2 raw35858step1; decide +kernel
      have hl : raw35858step1Labels = labelEmbedding6 ∘ raw35858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35858step1 raw35858step1Labels raw35858step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

def raw35859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35859 raw35859Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw35859 raw35859Labels = mixedMoment B raw35859step0 raw35859step0Labels := by
      have ha : raw35859step0 = (fun i j => raw35859 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35859step0 raw35859; decide +kernel
      have hl : raw35859step0Labels = raw35859Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35859 raw35859Labels permutation267 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw35860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35860 raw35860Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw35860 raw35860Labels = mixedMoment B raw35860step0 raw35860step0Labels := by
      have ha : raw35860step0 = (fun i j => raw35860 (permutation291 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35860step0 raw35860; decide +kernel
      have hl : raw35860step0Labels = raw35860Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35860 raw35860Labels permutation291 permutation2
    _ = mixedMoment B node5394 node5394Labels := by rfl

def raw35861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35861 raw35861Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw35861 raw35861Labels = mixedMoment B raw35861step0 raw35861step0Labels := by
      have ha : raw35861step0 = (fun i j => raw35861 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35861step0 raw35861; decide +kernel
      have hl : raw35861step0Labels = raw35861Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35861 raw35861Labels permutation265 permutation2
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw35862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw35862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35862 raw35862Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw35862 raw35862Labels = mixedMoment B raw35862step0 raw35862step0Labels := by
      have hz : ∀ j, raw35862 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35862step0 = (fun i j => raw35862 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35862step0 raw35862; decide +kernel
      have hl : raw35862step0Labels = raw35862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35862 raw35862Labels permutation520 hz
    mixedMoment B raw35862step0 raw35862step0Labels = mixedMoment B raw35862step1 raw35862step1Labels := by
      have ha : raw35862step1 = (fun i j => raw35862step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35862step1 raw35862step0; decide +kernel
      have hl : raw35862step1Labels = raw35862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35862step0 raw35862step0Labels permutation150 permutation2
    mixedMoment B raw35862step1 raw35862step1Labels = mixedMoment B raw35862step2 raw35862step2Labels := by
      have ha : raw35862step2 = -raw35862step1 := by apply Matrix.ext; change ∀ i j, raw35862step2 i j = -(raw35862step1 i j); unfold raw35862step2 raw35862step1; decide +kernel
      have hl : raw35862step2Labels = raw35862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw35863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35863step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35863step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35863step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35863 raw35863Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw35863 raw35863Labels = mixedMoment B raw35863step0 raw35863step0Labels := by
      have ha : raw35863step0 = (fun i j => raw35863 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35863step0 raw35863; decide +kernel
      have hl : raw35863step0Labels = raw35863Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35863 raw35863Labels permutation291 permutation7
    mixedMoment B raw35863step0 raw35863step0Labels = mixedMoment B raw35863step1 raw35863step1Labels := by
      have ha : raw35863step1 = -raw35863step0 := by apply Matrix.ext; change ∀ i j, raw35863step1 i j = -(raw35863step0 i j); unfold raw35863step1 raw35863step0; decide +kernel
      have hl : raw35863step1Labels = raw35863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35863step1 raw35863step1Labels = mixedMoment B raw35863step2 raw35863step2Labels := by
      have ha : raw35863step2 = raw35863step1 := by apply Matrix.ext; unfold raw35863step2 raw35863step1; decide +kernel
      have hl : raw35863step1Labels = labelEmbedding10 ∘ raw35863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35863step1 raw35863step1Labels raw35863step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw35864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35864step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35864 raw35864Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw35864 raw35864Labels = mixedMoment B raw35864step0 raw35864step0Labels := by
      have ha : raw35864step0 = (fun i j => raw35864 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35864step0 raw35864; decide +kernel
      have hl : raw35864step0Labels = raw35864Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35864 raw35864Labels permutation152 permutation3
    mixedMoment B raw35864step0 raw35864step0Labels = mixedMoment B raw35864step1 raw35864step1Labels := by
      have ha : raw35864step1 = raw35864step0 := by apply Matrix.ext; unfold raw35864step1 raw35864step0; decide +kernel
      have hl : raw35864step0Labels = labelEmbedding6 ∘ raw35864step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35864step0 raw35864step0Labels raw35864step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw35865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw35865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35865 raw35865Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw35865 raw35865Labels = mixedMoment B raw35865step0 raw35865step0Labels := by
      have ha : raw35865step0 = (fun i j => raw35865 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35865step0 raw35865; decide +kernel
      have hl : raw35865step0Labels = raw35865Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35865 raw35865Labels permutation664 permutation2
    mixedMoment B raw35865step0 raw35865step0Labels = mixedMoment B raw35865step1 raw35865step1Labels := by
      have ha : raw35865step1 = -raw35865step0 := by apply Matrix.ext; change ∀ i j, raw35865step1 i j = -(raw35865step0 i j); unfold raw35865step1 raw35865step0; decide +kernel
      have hl : raw35865step1Labels = raw35865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw35866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw35866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35866 raw35866Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw35866 raw35866Labels = mixedMoment B raw35866step0 raw35866step0Labels := by
      have ha : raw35866step0 = (fun i j => raw35866 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35866step0 raw35866; decide +kernel
      have hl : raw35866step0Labels = raw35866Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35866 raw35866Labels permutation688 permutation2
    mixedMoment B raw35866step0 raw35866step0Labels = mixedMoment B raw35866step1 raw35866step1Labels := by
      have ha : raw35866step1 = -raw35866step0 := by apply Matrix.ext; change ∀ i j, raw35866step1 i j = -(raw35866step0 i j); unfold raw35866step1 raw35866step0; decide +kernel
      have hl : raw35866step1Labels = raw35866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw35867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw35867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35867 raw35867Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw35867 raw35867Labels = mixedMoment B raw35867step0 raw35867step0Labels := by
      have hz : ∀ j, raw35867 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35867step0 = (fun i j => raw35867 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35867step0 raw35867; decide +kernel
      have hl : raw35867step0Labels = raw35867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35867 raw35867Labels permutation520 hz
    mixedMoment B raw35867step0 raw35867step0Labels = mixedMoment B raw35867step1 raw35867step1Labels := by
      have ha : raw35867step1 = (fun i j => raw35867step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35867step1 raw35867step0; decide +kernel
      have hl : raw35867step1Labels = raw35867step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35867step0 raw35867step0Labels permutation151 permutation2
    mixedMoment B raw35867step1 raw35867step1Labels = mixedMoment B raw35867step2 raw35867step2Labels := by
      have ha : raw35867step2 = -raw35867step1 := by apply Matrix.ext; change ∀ i j, raw35867step2 i j = -(raw35867step1 i j); unfold raw35867step2 raw35867step1; decide +kernel
      have hl : raw35867step2Labels = raw35867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw35868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35868step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35868 raw35868Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw35868 raw35868Labels = mixedMoment B raw35868step0 raw35868step0Labels := by
      have ha : raw35868step0 = (fun i j => raw35868 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35868step0 raw35868; decide +kernel
      have hl : raw35868step0Labels = raw35868Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35868 raw35868Labels permutation156 permutation3
    mixedMoment B raw35868step0 raw35868step0Labels = mixedMoment B raw35868step1 raw35868step1Labels := by
      have ha : raw35868step1 = raw35868step0 := by apply Matrix.ext; unfold raw35868step1 raw35868step0; decide +kernel
      have hl : raw35868step0Labels = labelEmbedding6 ∘ raw35868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35868step0 raw35868step0Labels raw35868step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw35869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35869step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35869 raw35869Labels = mixedMoment B node4680 node4680Labels := by
  calc
    mixedMoment B raw35869 raw35869Labels = mixedMoment B raw35869step0 raw35869step0Labels := by
      have ha : raw35869step0 = (fun i j => raw35869 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35869step0 raw35869; decide +kernel
      have hl : raw35869step0Labels = raw35869Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35869 raw35869Labels permutation160 permutation3
    mixedMoment B raw35869step0 raw35869step0Labels = mixedMoment B raw35869step1 raw35869step1Labels := by
      have ha : raw35869step1 = raw35869step0 := by apply Matrix.ext; unfold raw35869step1 raw35869step0; decide +kernel
      have hl : raw35869step0Labels = labelEmbedding6 ∘ raw35869step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35869step0 raw35869step0Labels raw35869step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4680 node4680Labels := by rfl

def raw35870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35870 raw35870Labels = mixedMoment B node4963 node4963Labels := by
  calc
    mixedMoment B raw35870 raw35870Labels = mixedMoment B raw35870step0 raw35870step0Labels := by
      have ha : raw35870step0 = (fun i j => raw35870 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35870step0 raw35870; decide +kernel
      have hl : raw35870step0Labels = raw35870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35870 raw35870Labels permutation267 permutation2
    _ = mixedMoment B node4963 node4963Labels := by rfl

def raw35871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35871step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35871 raw35871Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw35871 raw35871Labels = mixedMoment B raw35871step0 raw35871step0Labels := by
      have ha : raw35871step0 = (fun i j => raw35871 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35871step0 raw35871; decide +kernel
      have hl : raw35871step0Labels = raw35871Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35871 raw35871Labels permutation160 permutation3
    mixedMoment B raw35871step0 raw35871step0Labels = mixedMoment B raw35871step1 raw35871step1Labels := by
      have ha : raw35871step1 = raw35871step0 := by apply Matrix.ext; unfold raw35871step1 raw35871step0; decide +kernel
      have hl : raw35871step0Labels = labelEmbedding6 ∘ raw35871step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35871step0 raw35871step0Labels raw35871step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw35872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35872 raw35872Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw35872 raw35872Labels = mixedMoment B raw35872step0 raw35872step0Labels := by
      have hz : ∀ j, raw35872 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35872step0 = (fun i j => raw35872 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35872step0 raw35872; decide +kernel
      have hl : raw35872step0Labels = raw35872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35872 raw35872Labels permutation520 hz
    mixedMoment B raw35872step0 raw35872step0Labels = mixedMoment B raw35872step1 raw35872step1Labels := by
      have ha : raw35872step1 = (fun i j => raw35872step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35872step1 raw35872step0; decide +kernel
      have hl : raw35872step1Labels = raw35872step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35872step0 raw35872step0Labels permutation56 permutation2
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw35873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35873 raw35873Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw35873 raw35873Labels = mixedMoment B raw35873step0 raw35873step0Labels := by
      have ha : raw35873step0 = (fun i j => raw35873 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35873step0 raw35873; decide +kernel
      have hl : raw35873step0Labels = raw35873Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35873 raw35873Labels permutation267 permutation2
    _ = mixedMoment B node5382 node5382Labels := by rfl

def raw35874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35874step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35874 raw35874Labels = mixedMoment B node4668 node4668Labels := by
  calc
    mixedMoment B raw35874 raw35874Labels = mixedMoment B raw35874step0 raw35874step0Labels := by
      have ha : raw35874step0 = (fun i j => raw35874 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35874step0 raw35874; decide +kernel
      have hl : raw35874step0Labels = raw35874Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35874 raw35874Labels permutation155 permutation3
    mixedMoment B raw35874step0 raw35874step0Labels = mixedMoment B raw35874step1 raw35874step1Labels := by
      have ha : raw35874step1 = raw35874step0 := by apply Matrix.ext; unfold raw35874step1 raw35874step0; decide +kernel
      have hl : raw35874step0Labels = labelEmbedding6 ∘ raw35874step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35874step0 raw35874step0Labels raw35874step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4668 node4668Labels := by rfl

def raw35875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35875 raw35875Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw35875 raw35875Labels = mixedMoment B raw35875step0 raw35875step0Labels := by
      have ha : raw35875step0 = (fun i j => raw35875 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35875step0 raw35875; decide +kernel
      have hl : raw35875step0Labels = raw35875Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35875 raw35875Labels permutation267 permutation2
    _ = mixedMoment B node4955 node4955Labels := by rfl

def raw35876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35876 raw35876Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw35876 raw35876Labels = mixedMoment B raw35876step0 raw35876step0Labels := by
      have ha : raw35876step0 = (fun i j => raw35876 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35876step0 raw35876; decide +kernel
      have hl : raw35876step0Labels = raw35876Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35876 raw35876Labels permutation663 permutation2
    mixedMoment B raw35876step0 raw35876step0Labels = mixedMoment B raw35876step1 raw35876step1Labels := by
      have ha : raw35876step1 = -raw35876step0 := by apply Matrix.ext; change ∀ i j, raw35876step1 i j = -(raw35876step0 i j); unfold raw35876step1 raw35876step0; decide +kernel
      have hl : raw35876step1Labels = raw35876step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5336 node5336Labels := by rfl

def raw35877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35877step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35877step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35877 raw35877Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35877 raw35877Labels = mixedMoment B raw35877step0 raw35877step0Labels := by
      have hz : ∀ j, raw35877 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35877step0 = (fun i j => raw35877 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35877step0 raw35877; decide +kernel
      have hl : raw35877step0Labels = raw35877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35877 raw35877Labels permutation520 hz
    mixedMoment B raw35877step0 raw35877step0Labels = mixedMoment B raw35877step1 raw35877step1Labels := by
      have ha : raw35877step1 = (fun i j => raw35877step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35877step1 raw35877step0; decide +kernel
      have hl : raw35877step1Labels = raw35877step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35877step0 raw35877step0Labels permutation150 permutation2
    mixedMoment B raw35877step1 raw35877step1Labels = mixedMoment B raw35877step2 raw35877step2Labels := by
      have ha : raw35877step2 = -raw35877step1 := by apply Matrix.ext; change ∀ i j, raw35877step2 i j = -(raw35877step1 i j); unfold raw35877step2 raw35877step1; decide +kernel
      have hl : raw35877step2Labels = raw35877step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw35878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35878 raw35878Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw35878 raw35878Labels = mixedMoment B raw35878step0 raw35878step0Labels := by
      have ha : raw35878step0 = (fun i j => raw35878 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35878step0 raw35878; decide +kernel
      have hl : raw35878step0Labels = raw35878Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35878 raw35878Labels permutation268 permutation2
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw35879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35879step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35879 raw35879Labels = mixedMoment B node4665 node4665Labels := by
  calc
    mixedMoment B raw35879 raw35879Labels = mixedMoment B raw35879step0 raw35879step0Labels := by
      have ha : raw35879step0 = (fun i j => raw35879 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35879step0 raw35879; decide +kernel
      have hl : raw35879step0Labels = raw35879Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35879 raw35879Labels permutation153 permutation3
    mixedMoment B raw35879step0 raw35879step0Labels = mixedMoment B raw35879step1 raw35879step1Labels := by
      have ha : raw35879step1 = raw35879step0 := by apply Matrix.ext; unfold raw35879step1 raw35879step0; decide +kernel
      have hl : raw35879step0Labels = labelEmbedding6 ∘ raw35879step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35879step0 raw35879step0Labels raw35879step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4665 node4665Labels := by rfl

def raw35880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35880 raw35880Labels = mixedMoment B node4957 node4957Labels := by
  calc
    mixedMoment B raw35880 raw35880Labels = mixedMoment B raw35880step0 raw35880step0Labels := by
      have ha : raw35880step0 = (fun i j => raw35880 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35880step0 raw35880; decide +kernel
      have hl : raw35880step0Labels = raw35880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35880 raw35880Labels permutation265 permutation2
    _ = mixedMoment B node4957 node4957Labels := by rfl

def raw35881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35881 raw35881Labels = mixedMoment B node5372 node5372Labels := by
  calc
    mixedMoment B raw35881 raw35881Labels = mixedMoment B raw35881step0 raw35881step0Labels := by
      have ha : raw35881step0 = (fun i j => raw35881 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35881step0 raw35881; decide +kernel
      have hl : raw35881step0Labels = raw35881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35881 raw35881Labels permutation265 permutation2
    _ = mixedMoment B node5372 node5372Labels := by rfl

def raw35882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35882 raw35882Labels = mixedMoment B node5376 node5376Labels := by
  calc
    mixedMoment B raw35882 raw35882Labels = mixedMoment B raw35882step0 raw35882step0Labels := by
      have ha : raw35882step0 = (fun i j => raw35882 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35882step0 raw35882; decide +kernel
      have hl : raw35882step0Labels = raw35882Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35882 raw35882Labels permutation265 permutation2
    _ = mixedMoment B node5376 node5376Labels := by rfl

def raw35883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw35883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35883 raw35883Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw35883 raw35883Labels = mixedMoment B raw35883step0 raw35883step0Labels := by
      have ha : raw35883step0 = (fun i j => raw35883 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35883step0 raw35883; decide +kernel
      have hl : raw35883step0Labels = raw35883Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35883 raw35883Labels permutation266 permutation2
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw35884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw35884step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw35884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35884 raw35884Labels = mixedMoment B node4664 node4664Labels := by
  calc
    mixedMoment B raw35884 raw35884Labels = mixedMoment B raw35884step0 raw35884step0Labels := by
      have ha : raw35884step0 = (fun i j => raw35884 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35884step0 raw35884; decide +kernel
      have hl : raw35884step0Labels = raw35884Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35884 raw35884Labels permutation152 permutation3
    mixedMoment B raw35884step0 raw35884step0Labels = mixedMoment B raw35884step1 raw35884step1Labels := by
      have ha : raw35884step1 = raw35884step0 := by apply Matrix.ext; unfold raw35884step1 raw35884step0; decide +kernel
      have hl : raw35884step0Labels = labelEmbedding6 ∘ raw35884step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35884step0 raw35884step0Labels raw35884step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4664 node4664Labels := by rfl

def raw35885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw35885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35885 raw35885Labels = mixedMoment B node4954 node4954Labels := by
  calc
    mixedMoment B raw35885 raw35885Labels = mixedMoment B raw35885step0 raw35885step0Labels := by
      have ha : raw35885step0 = (fun i j => raw35885 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35885step0 raw35885; decide +kernel
      have hl : raw35885step0Labels = raw35885Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35885 raw35885Labels permutation267 permutation2
    _ = mixedMoment B node4954 node4954Labels := by rfl

def raw35886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35886 raw35886Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw35886 raw35886Labels = mixedMoment B raw35886step0 raw35886step0Labels := by
      have ha : raw35886step0 = (fun i j => raw35886 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35886step0 raw35886; decide +kernel
      have hl : raw35886step0Labels = raw35886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35886 raw35886Labels permutation663 permutation2
    mixedMoment B raw35886step0 raw35886step0Labels = mixedMoment B raw35886step1 raw35886step1Labels := by
      have ha : raw35886step1 = -raw35886step0 := by apply Matrix.ext; change ∀ i j, raw35886step1 i j = -(raw35886step0 i j); unfold raw35886step1 raw35886step0; decide +kernel
      have hl : raw35886step1Labels = raw35886step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5038 node5038Labels := by rfl

def raw35887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35887 raw35887Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw35887 raw35887Labels = mixedMoment B raw35887step0 raw35887step0Labels := by
      have ha : raw35887step0 = (fun i j => raw35887 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35887step0 raw35887; decide +kernel
      have hl : raw35887step0Labels = raw35887Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35887 raw35887Labels permutation687 permutation2
    mixedMoment B raw35887step0 raw35887step0Labels = mixedMoment B raw35887step1 raw35887step1Labels := by
      have ha : raw35887step1 = -raw35887step0 := by apply Matrix.ext; change ∀ i j, raw35887step1 i j = -(raw35887step0 i j); unfold raw35887step1 raw35887step0; decide +kernel
      have hl : raw35887step1Labels = raw35887step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw35888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw35888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw35888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35888 raw35888Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw35888 raw35888Labels = mixedMoment B raw35888step0 raw35888step0Labels := by
      have hz : ∀ j, raw35888 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35888step0 = (fun i j => raw35888 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35888step0 raw35888; decide +kernel
      have hl : raw35888step0Labels = raw35888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35888 raw35888Labels permutation520 hz
    mixedMoment B raw35888step0 raw35888step0Labels = mixedMoment B raw35888step1 raw35888step1Labels := by
      have ha : raw35888step1 = (fun i j => raw35888step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35888step1 raw35888step0; decide +kernel
      have hl : raw35888step1Labels = raw35888step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35888step0 raw35888step0Labels permutation150 permutation2
    mixedMoment B raw35888step1 raw35888step1Labels = mixedMoment B raw35888step2 raw35888step2Labels := by
      have ha : raw35888step2 = -raw35888step1 := by apply Matrix.ext; change ∀ i j, raw35888step2 i j = -(raw35888step1 i j); unfold raw35888step2 raw35888step1; decide +kernel
      have hl : raw35888step2Labels = raw35888step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw35889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35889Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35889step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35889step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35889step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35889 raw35889Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw35889 raw35889Labels = mixedMoment B raw35889step0 raw35889step0Labels := by
      have ha : raw35889step0 = (fun i j => raw35889 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35889step0 raw35889; decide +kernel
      have hl : raw35889step0Labels = raw35889Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35889 raw35889Labels permutation291 permutation7
    mixedMoment B raw35889step0 raw35889step0Labels = mixedMoment B raw35889step1 raw35889step1Labels := by
      have ha : raw35889step1 = -raw35889step0 := by apply Matrix.ext; change ∀ i j, raw35889step1 i j = -(raw35889step0 i j); unfold raw35889step1 raw35889step0; decide +kernel
      have hl : raw35889step1Labels = raw35889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35889step1 raw35889step1Labels = mixedMoment B raw35889step2 raw35889step2Labels := by
      have ha : raw35889step2 = raw35889step1 := by apply Matrix.ext; unfold raw35889step2 raw35889step1; decide +kernel
      have hl : raw35889step1Labels = labelEmbedding1 ∘ raw35889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35889step1 raw35889step1Labels raw35889step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw35890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35890Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35890 raw35890Labels = mixedMoment B node3793 node3793Labels := by
  calc
    mixedMoment B raw35890 raw35890Labels = mixedMoment B raw35890step0 raw35890step0Labels := by
      have ha : raw35890step0 = (fun i j => raw35890 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35890step0 raw35890; decide +kernel
      have hl : raw35890step0Labels = raw35890Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35890 raw35890Labels permutation660 permutation7
    mixedMoment B raw35890step0 raw35890step0Labels = mixedMoment B raw35890step1 raw35890step1Labels := by
      have ha : raw35890step1 = raw35890step0 := by apply Matrix.ext; unfold raw35890step1 raw35890step0; decide +kernel
      have hl : raw35890step0Labels = labelEmbedding1 ∘ raw35890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35890step0 raw35890step0Labels raw35890step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3793 node3793Labels := by rfl

def raw35891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35891step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35891 raw35891Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw35891 raw35891Labels = mixedMoment B raw35891step0 raw35891step0Labels := by
      have ha : raw35891step0 = (fun i j => raw35891 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35891step0 raw35891; decide +kernel
      have hl : raw35891step0Labels = raw35891Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35891 raw35891Labels permutation660 permutation7
    mixedMoment B raw35891step0 raw35891step0Labels = mixedMoment B raw35891step1 raw35891step1Labels := by
      have ha : raw35891step1 = raw35891step0 := by apply Matrix.ext; unfold raw35891step1 raw35891step0; decide +kernel
      have hl : raw35891step0Labels = labelEmbedding1 ∘ raw35891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35891step0 raw35891step0Labels raw35891step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw35892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35892 raw35892Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw35892 raw35892Labels = mixedMoment B raw35892step0 raw35892step0Labels := by
      have hz : ∀ j, raw35892 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35892step0 = (fun i j => raw35892 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35892step0 raw35892; decide +kernel
      have hl : raw35892step0Labels = raw35892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35892 raw35892Labels permutation520 hz
    mixedMoment B raw35892step0 raw35892step0Labels = mixedMoment B raw35892step1 raw35892step1Labels := by
      have ha : raw35892step1 = (fun i j => raw35892step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35892step1 raw35892step0; decide +kernel
      have hl : raw35892step1Labels = raw35892step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35892step0 raw35892step0Labels permutation147 permutation7
    mixedMoment B raw35892step1 raw35892step1Labels = mixedMoment B raw35892step2 raw35892step2Labels := by
      have ha : raw35892step2 = raw35892step1 := by apply Matrix.ext; unfold raw35892step2 raw35892step1; decide +kernel
      have hl : raw35892step1Labels = labelEmbedding1 ∘ raw35892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35892step1 raw35892step1Labels raw35892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw35893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35893step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35893step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35893step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35893 raw35893Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw35893 raw35893Labels = mixedMoment B raw35893step0 raw35893step0Labels := by
      have ha : raw35893step0 = (fun i j => raw35893 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35893step0 raw35893; decide +kernel
      have hl : raw35893step0Labels = raw35893Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35893 raw35893Labels permutation291 permutation7
    mixedMoment B raw35893step0 raw35893step0Labels = mixedMoment B raw35893step1 raw35893step1Labels := by
      have ha : raw35893step1 = -raw35893step0 := by apply Matrix.ext; change ∀ i j, raw35893step1 i j = -(raw35893step0 i j); unfold raw35893step1 raw35893step0; decide +kernel
      have hl : raw35893step1Labels = raw35893step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35893step1 raw35893step1Labels = mixedMoment B raw35893step2 raw35893step2Labels := by
      have ha : raw35893step2 = raw35893step1 := by apply Matrix.ext; unfold raw35893step2 raw35893step1; decide +kernel
      have hl : raw35893step1Labels = labelEmbedding1 ∘ raw35893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35893step1 raw35893step1Labels raw35893step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw35894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw35894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35894step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35894step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35894 raw35894Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw35894 raw35894Labels = mixedMoment B raw35894step0 raw35894step0Labels := by
      have ha : raw35894step0 = (fun i j => raw35894 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35894step0 raw35894; decide +kernel
      have hl : raw35894step0Labels = raw35894Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35894 raw35894Labels permutation218 permutation5
    mixedMoment B raw35894step0 raw35894step0Labels = mixedMoment B raw35894step1 raw35894step1Labels := by
      have ha : raw35894step1 = -raw35894step0 := by apply Matrix.ext; change ∀ i j, raw35894step1 i j = -(raw35894step0 i j); unfold raw35894step1 raw35894step0; decide +kernel
      have hl : raw35894step1Labels = raw35894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35894step1 raw35894step1Labels = mixedMoment B raw35894step2 raw35894step2Labels := by
      have ha : raw35894step2 = raw35894step1 := by apply Matrix.ext; unfold raw35894step2 raw35894step1; decide +kernel
      have hl : raw35894step1Labels = labelEmbedding1 ∘ raw35894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35894step1 raw35894step1Labels raw35894step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw35895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35895step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35895 raw35895Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw35895 raw35895Labels = mixedMoment B raw35895step0 raw35895step0Labels := by
      have ha : raw35895step0 = (fun i j => raw35895 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35895step0 raw35895; decide +kernel
      have hl : raw35895step0Labels = raw35895Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35895 raw35895Labels permutation660 permutation7
    mixedMoment B raw35895step0 raw35895step0Labels = mixedMoment B raw35895step1 raw35895step1Labels := by
      have ha : raw35895step1 = raw35895step0 := by apply Matrix.ext; unfold raw35895step1 raw35895step0; decide +kernel
      have hl : raw35895step0Labels = labelEmbedding1 ∘ raw35895step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35895step0 raw35895step0Labels raw35895step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw35896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35896step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35896step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35896 raw35896Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw35896 raw35896Labels = mixedMoment B raw35896step0 raw35896step0Labels := by
      have ha : raw35896step0 = (fun i j => raw35896 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35896step0 raw35896; decide +kernel
      have hl : raw35896step0Labels = raw35896Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35896 raw35896Labels permutation660 permutation7
    mixedMoment B raw35896step0 raw35896step0Labels = mixedMoment B raw35896step1 raw35896step1Labels := by
      have ha : raw35896step1 = raw35896step0 := by apply Matrix.ext; unfold raw35896step1 raw35896step0; decide +kernel
      have hl : raw35896step0Labels = labelEmbedding1 ∘ raw35896step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35896step0 raw35896step0Labels raw35896step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw35897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35897step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35897step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35897step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35897 raw35897Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw35897 raw35897Labels = mixedMoment B raw35897step0 raw35897step0Labels := by
      have hz : ∀ j, raw35897 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35897step0 = (fun i j => raw35897 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35897step0 raw35897; decide +kernel
      have hl : raw35897step0Labels = raw35897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35897 raw35897Labels permutation520 hz
    mixedMoment B raw35897step0 raw35897step0Labels = mixedMoment B raw35897step1 raw35897step1Labels := by
      have ha : raw35897step1 = (fun i j => raw35897step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35897step1 raw35897step0; decide +kernel
      have hl : raw35897step1Labels = raw35897step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35897step0 raw35897step0Labels permutation147 permutation7
    mixedMoment B raw35897step1 raw35897step1Labels = mixedMoment B raw35897step2 raw35897step2Labels := by
      have ha : raw35897step2 = raw35897step1 := by apply Matrix.ext; unfold raw35897step2 raw35897step1; decide +kernel
      have hl : raw35897step1Labels = labelEmbedding1 ∘ raw35897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35897step1 raw35897step1Labels raw35897step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw35898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw35898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35898 raw35898Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw35898 raw35898Labels = mixedMoment B raw35898step0 raw35898step0Labels := by
      have ha : raw35898step0 = (fun i j => raw35898 (permutation257 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35898step0 raw35898; decide +kernel
      have hl : raw35898step0Labels = raw35898Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35898 raw35898Labels permutation257 permutation5
    mixedMoment B raw35898step0 raw35898step0Labels = mixedMoment B raw35898step1 raw35898step1Labels := by
      have ha : raw35898step1 = -raw35898step0 := by apply Matrix.ext; change ∀ i j, raw35898step1 i j = -(raw35898step0 i j); unfold raw35898step1 raw35898step0; decide +kernel
      have hl : raw35898step1Labels = raw35898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35898step1 raw35898step1Labels = mixedMoment B raw35898step2 raw35898step2Labels := by
      have ha : raw35898step2 = raw35898step1 := by apply Matrix.ext; unfold raw35898step2 raw35898step1; decide +kernel
      have hl : raw35898step1Labels = labelEmbedding1 ∘ raw35898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35898step1 raw35898step1Labels raw35898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw35899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35899step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35899step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35899 raw35899Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw35899 raw35899Labels = mixedMoment B raw35899step0 raw35899step0Labels := by
      have ha : raw35899step0 = (fun i j => raw35899 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35899step0 raw35899; decide +kernel
      have hl : raw35899step0Labels = raw35899Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35899 raw35899Labels permutation163 permutation5
    mixedMoment B raw35899step0 raw35899step0Labels = mixedMoment B raw35899step1 raw35899step1Labels := by
      have ha : raw35899step1 = -raw35899step0 := by apply Matrix.ext; change ∀ i j, raw35899step1 i j = -(raw35899step0 i j); unfold raw35899step1 raw35899step0; decide +kernel
      have hl : raw35899step1Labels = raw35899step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35899step1 raw35899step1Labels = mixedMoment B raw35899step2 raw35899step2Labels := by
      have ha : raw35899step2 = raw35899step1 := by apply Matrix.ext; unfold raw35899step2 raw35899step1; decide +kernel
      have hl : raw35899step1Labels = labelEmbedding1 ∘ raw35899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35899step1 raw35899step1Labels raw35899step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

def raw35900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35900step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35900step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35900step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35900step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35900 raw35900Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw35900 raw35900Labels = mixedMoment B raw35900step0 raw35900step0Labels := by
      have ha : raw35900step0 = (fun i j => raw35900 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35900step0 raw35900; decide +kernel
      have hl : raw35900step0Labels = raw35900Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35900 raw35900Labels permutation291 permutation7
    mixedMoment B raw35900step0 raw35900step0Labels = mixedMoment B raw35900step1 raw35900step1Labels := by
      have ha : raw35900step1 = -raw35900step0 := by apply Matrix.ext; change ∀ i j, raw35900step1 i j = -(raw35900step0 i j); unfold raw35900step1 raw35900step0; decide +kernel
      have hl : raw35900step1Labels = raw35900step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35900step1 raw35900step1Labels = mixedMoment B raw35900step2 raw35900step2Labels := by
      have ha : raw35900step2 = raw35900step1 := by apply Matrix.ext; unfold raw35900step2 raw35900step1; decide +kernel
      have hl : raw35900step1Labels = labelEmbedding1 ∘ raw35900step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35900step1 raw35900step1Labels raw35900step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

def raw35901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35901step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35901step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35901step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35901step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35901 raw35901Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw35901 raw35901Labels = mixedMoment B raw35901step0 raw35901step0Labels := by
      have ha : raw35901step0 = (fun i j => raw35901 (permutation205 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35901step0 raw35901; decide +kernel
      have hl : raw35901step0Labels = raw35901Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35901 raw35901Labels permutation205 permutation5
    mixedMoment B raw35901step0 raw35901step0Labels = mixedMoment B raw35901step1 raw35901step1Labels := by
      have ha : raw35901step1 = -raw35901step0 := by apply Matrix.ext; change ∀ i j, raw35901step1 i j = -(raw35901step0 i j); unfold raw35901step1 raw35901step0; decide +kernel
      have hl : raw35901step1Labels = raw35901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35901step1 raw35901step1Labels = mixedMoment B raw35901step2 raw35901step2Labels := by
      have ha : raw35901step2 = raw35901step1 := by apply Matrix.ext; unfold raw35901step2 raw35901step1; decide +kernel
      have hl : raw35901step1Labels = labelEmbedding1 ∘ raw35901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35901step1 raw35901step1Labels raw35901step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw35902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35902step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35902 raw35902Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw35902 raw35902Labels = mixedMoment B raw35902step0 raw35902step0Labels := by
      have hz : ∀ j, raw35902 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35902step0 = (fun i j => raw35902 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35902step0 raw35902; decide +kernel
      have hl : raw35902step0Labels = raw35902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35902 raw35902Labels permutation520 hz
    mixedMoment B raw35902step0 raw35902step0Labels = mixedMoment B raw35902step1 raw35902step1Labels := by
      have ha : raw35902step1 = (fun i j => raw35902step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35902step1 raw35902step0; decide +kernel
      have hl : raw35902step1Labels = raw35902step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35902step0 raw35902step0Labels permutation147 permutation7
    mixedMoment B raw35902step1 raw35902step1Labels = mixedMoment B raw35902step2 raw35902step2Labels := by
      have ha : raw35902step2 = raw35902step1 := by apply Matrix.ext; unfold raw35902step2 raw35902step1; decide +kernel
      have hl : raw35902step1Labels = labelEmbedding1 ∘ raw35902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35902step1 raw35902step1Labels raw35902step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw35903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35903Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35903step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35903step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35903step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35903 raw35903Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw35903 raw35903Labels = mixedMoment B raw35903step0 raw35903step0Labels := by
      have ha : raw35903step0 = (fun i j => raw35903 (permutation249 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35903step0 raw35903; decide +kernel
      have hl : raw35903step0Labels = raw35903Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35903 raw35903Labels permutation249 permutation5
    mixedMoment B raw35903step0 raw35903step0Labels = mixedMoment B raw35903step1 raw35903step1Labels := by
      have ha : raw35903step1 = -raw35903step0 := by apply Matrix.ext; change ∀ i j, raw35903step1 i j = -(raw35903step0 i j); unfold raw35903step1 raw35903step0; decide +kernel
      have hl : raw35903step1Labels = raw35903step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35903step1 raw35903step1Labels = mixedMoment B raw35903step2 raw35903step2Labels := by
      have ha : raw35903step2 = raw35903step1 := by apply Matrix.ext; unfold raw35903step2 raw35903step1; decide +kernel
      have hl : raw35903step1Labels = labelEmbedding1 ∘ raw35903step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35903step1 raw35903step1Labels raw35903step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3866 node3866Labels := by rfl

def raw35904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35904Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35904step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35904step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35904step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35904 raw35904Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw35904 raw35904Labels = mixedMoment B raw35904step0 raw35904step0Labels := by
      have ha : raw35904step0 = (fun i j => raw35904 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35904step0 raw35904; decide +kernel
      have hl : raw35904step0Labels = raw35904Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35904 raw35904Labels permutation171 permutation5
    mixedMoment B raw35904step0 raw35904step0Labels = mixedMoment B raw35904step1 raw35904step1Labels := by
      have ha : raw35904step1 = -raw35904step0 := by apply Matrix.ext; change ∀ i j, raw35904step1 i j = -(raw35904step0 i j); unfold raw35904step1 raw35904step0; decide +kernel
      have hl : raw35904step1Labels = raw35904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35904step1 raw35904step1Labels = mixedMoment B raw35904step2 raw35904step2Labels := by
      have ha : raw35904step2 = raw35904step1 := by apply Matrix.ext; unfold raw35904step2 raw35904step1; decide +kernel
      have hl : raw35904step1Labels = labelEmbedding1 ∘ raw35904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35904step1 raw35904step1Labels raw35904step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

def raw35905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35905Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35905step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35905step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35905step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35905 raw35905Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw35905 raw35905Labels = mixedMoment B raw35905step0 raw35905step0Labels := by
      have ha : raw35905step0 = (fun i j => raw35905 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35905step0 raw35905; decide +kernel
      have hl : raw35905step0Labels = raw35905Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35905 raw35905Labels permutation291 permutation7
    mixedMoment B raw35905step0 raw35905step0Labels = mixedMoment B raw35905step1 raw35905step1Labels := by
      have ha : raw35905step1 = -raw35905step0 := by apply Matrix.ext; change ∀ i j, raw35905step1 i j = -(raw35905step0 i j); unfold raw35905step1 raw35905step0; decide +kernel
      have hl : raw35905step1Labels = raw35905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35905step1 raw35905step1Labels = mixedMoment B raw35905step2 raw35905step2Labels := by
      have ha : raw35905step2 = raw35905step1 := by apply Matrix.ext; unfold raw35905step2 raw35905step1; decide +kernel
      have hl : raw35905step1Labels = labelEmbedding1 ∘ raw35905step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35905step1 raw35905step1Labels raw35905step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

def raw35906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35906Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35906step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35906 raw35906Labels = mixedMoment B node3754 node3754Labels := by
  calc
    mixedMoment B raw35906 raw35906Labels = mixedMoment B raw35906step0 raw35906step0Labels := by
      have ha : raw35906step0 = (fun i j => raw35906 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35906step0 raw35906; decide +kernel
      have hl : raw35906step0Labels = raw35906Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35906 raw35906Labels permutation660 permutation7
    mixedMoment B raw35906step0 raw35906step0Labels = mixedMoment B raw35906step1 raw35906step1Labels := by
      have ha : raw35906step1 = raw35906step0 := by apply Matrix.ext; unfold raw35906step1 raw35906step0; decide +kernel
      have hl : raw35906step0Labels = labelEmbedding1 ∘ raw35906step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35906step0 raw35906step0Labels raw35906step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3754 node3754Labels := by rfl

def raw35907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35907Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35907step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35907 raw35907Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw35907 raw35907Labels = mixedMoment B raw35907step0 raw35907step0Labels := by
      have hz : ∀ j, raw35907 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35907step0 = (fun i j => raw35907 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35907step0 raw35907; decide +kernel
      have hl : raw35907step0Labels = raw35907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35907 raw35907Labels permutation520 hz
    mixedMoment B raw35907step0 raw35907step0Labels = mixedMoment B raw35907step1 raw35907step1Labels := by
      have ha : raw35907step1 = (fun i j => raw35907step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35907step1 raw35907step0; decide +kernel
      have hl : raw35907step1Labels = raw35907step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35907step0 raw35907step0Labels permutation147 permutation7
    mixedMoment B raw35907step1 raw35907step1Labels = mixedMoment B raw35907step2 raw35907step2Labels := by
      have ha : raw35907step2 = raw35907step1 := by apply Matrix.ext; unfold raw35907step2 raw35907step1; decide +kernel
      have hl : raw35907step1Labels = labelEmbedding1 ∘ raw35907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35907step1 raw35907step1Labels raw35907step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw35908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35908Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35908step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35908step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35908step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35908 raw35908Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw35908 raw35908Labels = mixedMoment B raw35908step0 raw35908step0Labels := by
      have ha : raw35908step0 = (fun i j => raw35908 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35908step0 raw35908; decide +kernel
      have hl : raw35908step0Labels = raw35908Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35908 raw35908Labels permutation291 permutation7
    mixedMoment B raw35908step0 raw35908step0Labels = mixedMoment B raw35908step1 raw35908step1Labels := by
      have ha : raw35908step1 = -raw35908step0 := by apply Matrix.ext; change ∀ i j, raw35908step1 i j = -(raw35908step0 i j); unfold raw35908step1 raw35908step0; decide +kernel
      have hl : raw35908step1Labels = raw35908step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35908step1 raw35908step1Labels = mixedMoment B raw35908step2 raw35908step2Labels := by
      have ha : raw35908step2 = raw35908step1 := by apply Matrix.ext; unfold raw35908step2 raw35908step1; decide +kernel
      have hl : raw35908step1Labels = labelEmbedding1 ∘ raw35908step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35908step1 raw35908step1Labels raw35908step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw35909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35909Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw35909step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35909step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35909step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35909step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35909step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35909 raw35909Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw35909 raw35909Labels = mixedMoment B raw35909step0 raw35909step0Labels := by
      have ha : raw35909step0 = (fun i j => raw35909 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35909step0 raw35909; decide +kernel
      have hl : raw35909step0Labels = raw35909Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35909 raw35909Labels permutation162 permutation5
    mixedMoment B raw35909step0 raw35909step0Labels = mixedMoment B raw35909step1 raw35909step1Labels := by
      have ha : raw35909step1 = -raw35909step0 := by apply Matrix.ext; change ∀ i j, raw35909step1 i j = -(raw35909step0 i j); unfold raw35909step1 raw35909step0; decide +kernel
      have hl : raw35909step1Labels = raw35909step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35909step1 raw35909step1Labels = mixedMoment B raw35909step2 raw35909step2Labels := by
      have ha : raw35909step2 = raw35909step1 := by apply Matrix.ext; unfold raw35909step2 raw35909step1; decide +kernel
      have hl : raw35909step1Labels = labelEmbedding1 ∘ raw35909step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35909step1 raw35909step1Labels raw35909step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

def raw35910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35910Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw35910step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35910step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35910step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35910step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35910 raw35910Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw35910 raw35910Labels = mixedMoment B raw35910step0 raw35910step0Labels := by
      have ha : raw35910step0 = (fun i j => raw35910 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35910step0 raw35910; decide +kernel
      have hl : raw35910step0Labels = raw35910Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35910 raw35910Labels permutation291 permutation7
    mixedMoment B raw35910step0 raw35910step0Labels = mixedMoment B raw35910step1 raw35910step1Labels := by
      have ha : raw35910step1 = -raw35910step0 := by apply Matrix.ext; change ∀ i j, raw35910step1 i j = -(raw35910step0 i j); unfold raw35910step1 raw35910step0; decide +kernel
      have hl : raw35910step1Labels = raw35910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35910step1 raw35910step1Labels = mixedMoment B raw35910step2 raw35910step2Labels := by
      have ha : raw35910step2 = raw35910step1 := by apply Matrix.ext; unfold raw35910step2 raw35910step1; decide +kernel
      have hl : raw35910step1Labels = labelEmbedding1 ∘ raw35910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35910step1 raw35910step1Labels raw35910step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

def raw35911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35911Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35911step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35911 raw35911Labels = mixedMoment B node3791 node3791Labels := by
  calc
    mixedMoment B raw35911 raw35911Labels = mixedMoment B raw35911step0 raw35911step0Labels := by
      have ha : raw35911step0 = (fun i j => raw35911 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35911step0 raw35911; decide +kernel
      have hl : raw35911step0Labels = raw35911Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35911 raw35911Labels permutation660 permutation7
    mixedMoment B raw35911step0 raw35911step0Labels = mixedMoment B raw35911step1 raw35911step1Labels := by
      have ha : raw35911step1 = raw35911step0 := by apply Matrix.ext; unfold raw35911step1 raw35911step0; decide +kernel
      have hl : raw35911step0Labels = labelEmbedding1 ∘ raw35911step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35911step0 raw35911step0Labels raw35911step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3791 node3791Labels := by rfl

def raw35912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35912Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35912step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35912 raw35912Labels = mixedMoment B node3833 node3833Labels := by
  calc
    mixedMoment B raw35912 raw35912Labels = mixedMoment B raw35912step0 raw35912step0Labels := by
      have ha : raw35912step0 = (fun i j => raw35912 (permutation550 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35912step0 raw35912; decide +kernel
      have hl : raw35912step0Labels = raw35912Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35912 raw35912Labels permutation550 permutation5
    mixedMoment B raw35912step0 raw35912step0Labels = mixedMoment B raw35912step1 raw35912step1Labels := by
      have ha : raw35912step1 = raw35912step0 := by apply Matrix.ext; unfold raw35912step1 raw35912step0; decide +kernel
      have hl : raw35912step0Labels = labelEmbedding1 ∘ raw35912step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35912step0 raw35912step0Labels raw35912step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3833 node3833Labels := by rfl

def raw35913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw35913Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35913step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35913step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35913step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35913 raw35913Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw35913 raw35913Labels = mixedMoment B raw35913step0 raw35913step0Labels := by
      have ha : raw35913step0 = (fun i j => raw35913 (permutation291 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35913step0 raw35913; decide +kernel
      have hl : raw35913step0Labels = raw35913Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35913 raw35913Labels permutation291 permutation7
    mixedMoment B raw35913step0 raw35913step0Labels = mixedMoment B raw35913step1 raw35913step1Labels := by
      have ha : raw35913step1 = -raw35913step0 := by apply Matrix.ext; change ∀ i j, raw35913step1 i j = -(raw35913step0 i j); unfold raw35913step1 raw35913step0; decide +kernel
      have hl : raw35913step1Labels = raw35913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35913step1 raw35913step1Labels = mixedMoment B raw35913step2 raw35913step2Labels := by
      have ha : raw35913step2 = raw35913step1 := by apply Matrix.ext; unfold raw35913step2 raw35913step1; decide +kernel
      have hl : raw35913step1Labels = labelEmbedding1 ∘ raw35913step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35913step1 raw35913step1Labels raw35913step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw35914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35914Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw35914step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw35914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35914step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw35914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35914 raw35914Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw35914 raw35914Labels = mixedMoment B raw35914step0 raw35914step0Labels := by
      have ha : raw35914step0 = (fun i j => raw35914 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35914step0 raw35914; decide +kernel
      have hl : raw35914step0Labels = raw35914Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35914 raw35914Labels permutation158 permutation5
    mixedMoment B raw35914step0 raw35914step0Labels = mixedMoment B raw35914step1 raw35914step1Labels := by
      have ha : raw35914step1 = -raw35914step0 := by apply Matrix.ext; change ∀ i j, raw35914step1 i j = -(raw35914step0 i j); unfold raw35914step1 raw35914step0; decide +kernel
      have hl : raw35914step1Labels = raw35914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35914step1 raw35914step1Labels = mixedMoment B raw35914step2 raw35914step2Labels := by
      have ha : raw35914step2 = raw35914step1 := by apply Matrix.ext; unfold raw35914step2 raw35914step1; decide +kernel
      have hl : raw35914step1Labels = labelEmbedding1 ∘ raw35914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35914step1 raw35914step1Labels raw35914step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

def raw35915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35915Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35915step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35915 raw35915Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw35915 raw35915Labels = mixedMoment B raw35915step0 raw35915step0Labels := by
      have ha : raw35915step0 = (fun i j => raw35915 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35915step0 raw35915; decide +kernel
      have hl : raw35915step0Labels = raw35915Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35915 raw35915Labels permutation660 permutation7
    mixedMoment B raw35915step0 raw35915step0Labels = mixedMoment B raw35915step1 raw35915step1Labels := by
      have ha : raw35915step1 = raw35915step0 := by apply Matrix.ext; unfold raw35915step1 raw35915step0; decide +kernel
      have hl : raw35915step0Labels = labelEmbedding1 ∘ raw35915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35915step0 raw35915step0Labels raw35915step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

def raw35916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35916Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35916step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35916 raw35916Labels = mixedMoment B node3453 node3453Labels := by
  calc
    mixedMoment B raw35916 raw35916Labels = mixedMoment B raw35916step0 raw35916step0Labels := by
      have ha : raw35916step0 = (fun i j => raw35916 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35916step0 raw35916; decide +kernel
      have hl : raw35916step0Labels = raw35916Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35916 raw35916Labels permutation660 permutation7
    mixedMoment B raw35916step0 raw35916step0Labels = mixedMoment B raw35916step1 raw35916step1Labels := by
      have ha : raw35916step1 = raw35916step0 := by apply Matrix.ext; unfold raw35916step1 raw35916step0; decide +kernel
      have hl : raw35916step0Labels = labelEmbedding1 ∘ raw35916step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35916step0 raw35916step0Labels raw35916step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3453 node3453Labels := by rfl

def raw35917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35917Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35917step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35917 raw35917Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw35917 raw35917Labels = mixedMoment B raw35917step0 raw35917step0Labels := by
      have ha : raw35917step0 = (fun i j => raw35917 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35917step0 raw35917; decide +kernel
      have hl : raw35917step0Labels = raw35917Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35917 raw35917Labels permutation660 permutation7
    mixedMoment B raw35917step0 raw35917step0Labels = mixedMoment B raw35917step1 raw35917step1Labels := by
      have ha : raw35917step1 = raw35917step0 := by apply Matrix.ext; unfold raw35917step1 raw35917step0; decide +kernel
      have hl : raw35917step0Labels = labelEmbedding1 ∘ raw35917step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35917step0 raw35917step0Labels raw35917step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw35918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw35918Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw35918step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35918step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35918step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35918 raw35918Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw35918 raw35918Labels = mixedMoment B raw35918step0 raw35918step0Labels := by
      have hz : ∀ j, raw35918 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35918step0 = (fun i j => raw35918 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35918step0 raw35918; decide +kernel
      have hl : raw35918step0Labels = raw35918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35918 raw35918Labels permutation520 hz
    mixedMoment B raw35918step0 raw35918step0Labels = mixedMoment B raw35918step1 raw35918step1Labels := by
      have ha : raw35918step1 = (fun i j => raw35918step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35918step1 raw35918step0; decide +kernel
      have hl : raw35918step1Labels = raw35918step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35918step0 raw35918step0Labels permutation147 permutation7
    mixedMoment B raw35918step1 raw35918step1Labels = mixedMoment B raw35918step2 raw35918step2Labels := by
      have ha : raw35918step2 = raw35918step1 := by apply Matrix.ext; unfold raw35918step2 raw35918step1; decide +kernel
      have hl : raw35918step1Labels = labelEmbedding1 ∘ raw35918step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35918step1 raw35918step1Labels raw35918step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw35919 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35919step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35919step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35919step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35919step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35919 raw35919Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw35919 raw35919Labels = mixedMoment B raw35919step0 raw35919step0Labels := by
      have ha : raw35919step0 = (fun i j => raw35919 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35919step0 raw35919; decide +kernel
      have hl : raw35919step0Labels = raw35919Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35919 raw35919Labels permutation663 permutation7
    mixedMoment B raw35919step0 raw35919step0Labels = mixedMoment B raw35919step1 raw35919step1Labels := by
      have ha : raw35919step1 = -raw35919step0 := by apply Matrix.ext; change ∀ i j, raw35919step1 i j = -(raw35919step0 i j); unfold raw35919step1 raw35919step0; decide +kernel
      have hl : raw35919step1Labels = raw35919step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35919step1 raw35919step1Labels = mixedMoment B raw35919step2 raw35919step2Labels := by
      have ha : raw35919step2 = raw35919step1 := by apply Matrix.ext; unfold raw35919step2 raw35919step1; decide +kernel
      have hl : raw35919step1Labels = labelEmbedding10 ∘ raw35919step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35919step1 raw35919step1Labels raw35919step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw35920 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35920 raw35920Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw35920 raw35920Labels = mixedMoment B raw35920step0 raw35920step0Labels := by
      have ha : raw35920step0 = (fun i j => raw35920 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35920step0 raw35920; decide +kernel
      have hl : raw35920step0Labels = raw35920Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35920 raw35920Labels permutation663 permutation2
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw35921 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw35921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35921 raw35921Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw35921 raw35921Labels = mixedMoment B raw35921step0 raw35921step0Labels := by
      have ha : raw35921step0 = (fun i j => raw35921 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35921step0 raw35921; decide +kernel
      have hl : raw35921step0Labels = raw35921Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35921 raw35921Labels permutation663 permutation2
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw35922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw35922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw35922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35922 raw35922Labels = mixedMoment B node5143 node5143Labels := by
  calc
    mixedMoment B raw35922 raw35922Labels = mixedMoment B raw35922step0 raw35922step0Labels := by
      have ha : raw35922step0 = (fun i j => raw35922 (permutation299 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35922step0 raw35922; decide +kernel
      have hl : raw35922step0Labels = raw35922Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35922 raw35922Labels permutation299 permutation2
    mixedMoment B raw35922step0 raw35922step0Labels = mixedMoment B raw35922step1 raw35922step1Labels := by
      have ha : raw35922step1 = -raw35922step0 := by apply Matrix.ext; change ∀ i j, raw35922step1 i j = -(raw35922step0 i j); unfold raw35922step1 raw35922step0; decide +kernel
      have hl : raw35922step1Labels = raw35922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5143 node5143Labels := by rfl

def raw35923 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35923step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35923 raw35923Labels = mixedMoment B node5121 node5121Labels := by
  calc
    mixedMoment B raw35923 raw35923Labels = mixedMoment B raw35923step0 raw35923step0Labels := by
      have ha : raw35923step0 = (fun i j => raw35923 (permutation291 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35923step0 raw35923; decide +kernel
      have hl : raw35923step0Labels = raw35923Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35923 raw35923Labels permutation291 permutation2
    mixedMoment B raw35923step0 raw35923step0Labels = mixedMoment B raw35923step1 raw35923step1Labels := by
      have ha : raw35923step1 = -raw35923step0 := by apply Matrix.ext; change ∀ i j, raw35923step1 i j = -(raw35923step0 i j); unfold raw35923step1 raw35923step0; decide +kernel
      have hl : raw35923step1Labels = raw35923step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5121 node5121Labels := by rfl

def raw35924 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw35924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw35924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35924 raw35924Labels = mixedMoment B node5051 node5051Labels := by
  calc
    mixedMoment B raw35924 raw35924Labels = mixedMoment B raw35924step0 raw35924step0Labels := by
      have ha : raw35924step0 = (fun i j => raw35924 (permutation660 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35924step0 raw35924; decide +kernel
      have hl : raw35924step0Labels = raw35924Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35924 raw35924Labels permutation660 permutation2
    _ = mixedMoment B node5051 node5051Labels := by rfl

def raw35925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw35925step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw35925step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35925step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw35925step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35925 raw35925Labels = mixedMoment B node5224 node5224Labels := by
  calc
    mixedMoment B raw35925 raw35925Labels = mixedMoment B raw35925step0 raw35925step0Labels := by
      have ha : raw35925step0 = (fun i j => raw35925 (permutation163 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35925step0 raw35925; decide +kernel
      have hl : raw35925step0Labels = raw35925Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35925 raw35925Labels permutation163 permutation4
    mixedMoment B raw35925step0 raw35925step0Labels = mixedMoment B raw35925step1 raw35925step1Labels := by
      have ha : raw35925step1 = -raw35925step0 := by apply Matrix.ext; change ∀ i j, raw35925step1 i j = -(raw35925step0 i j); unfold raw35925step1 raw35925step0; decide +kernel
      have hl : raw35925step1Labels = raw35925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35925step1 raw35925step1Labels = mixedMoment B raw35925step2 raw35925step2Labels := by
      have ha : raw35925step2 = raw35925step1 := by apply Matrix.ext; unfold raw35925step2 raw35925step1; decide +kernel
      have hl : raw35925step1Labels = labelEmbedding7 ∘ raw35925step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35925step1 raw35925step1Labels raw35925step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5224 node5224Labels := by rfl

def raw35926 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35926step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35926 raw35926Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw35926 raw35926Labels = mixedMoment B raw35926step0 raw35926step0Labels := by
      have ha : raw35926step0 = (fun i j => raw35926 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35926step0 raw35926; decide +kernel
      have hl : raw35926step0Labels = raw35926Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35926 raw35926Labels permutation152 permutation6
    mixedMoment B raw35926step0 raw35926step0Labels = mixedMoment B raw35926step1 raw35926step1Labels := by
      have ha : raw35926step1 = raw35926step0 := by apply Matrix.ext; unfold raw35926step1 raw35926step0; decide +kernel
      have hl : raw35926step0Labels = labelEmbedding9 ∘ raw35926step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35926step0 raw35926step0Labels raw35926step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw35927 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35927 raw35927Labels = mixedMoment B node5342 node5342Labels := by
  calc
    mixedMoment B raw35927 raw35927Labels = mixedMoment B raw35927step0 raw35927step0Labels := by
      have ha : raw35927step0 = (fun i j => raw35927 (permutation660 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35927step0 raw35927; decide +kernel
      have hl : raw35927step0Labels = raw35927Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35927 raw35927Labels permutation660 permutation2
    _ = mixedMoment B node5342 node5342Labels := by rfl

def raw35928 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw35928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35928 raw35928Labels = mixedMoment B node5053 node5053Labels := by
  calc
    mixedMoment B raw35928 raw35928Labels = mixedMoment B raw35928step0 raw35928step0Labels := by
      have ha : raw35928step0 = (fun i j => raw35928 (permutation660 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35928step0 raw35928; decide +kernel
      have hl : raw35928step0Labels = raw35928Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35928 raw35928Labels permutation660 permutation2
    _ = mixedMoment B node5053 node5053Labels := by rfl

def raw35929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw35929step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35929step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35929step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35929step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35929 raw35929Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw35929 raw35929Labels = mixedMoment B raw35929step0 raw35929step0Labels := by
      have ha : raw35929step0 = (fun i j => raw35929 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35929step0 raw35929; decide +kernel
      have hl : raw35929step0Labels = raw35929Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35929 raw35929Labels permutation170 permutation4
    mixedMoment B raw35929step0 raw35929step0Labels = mixedMoment B raw35929step1 raw35929step1Labels := by
      have ha : raw35929step1 = -raw35929step0 := by apply Matrix.ext; change ∀ i j, raw35929step1 i j = -(raw35929step0 i j); unfold raw35929step1 raw35929step0; decide +kernel
      have hl : raw35929step1Labels = raw35929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35929step1 raw35929step1Labels = mixedMoment B raw35929step2 raw35929step2Labels := by
      have ha : raw35929step2 = raw35929step1 := by apply Matrix.ext; unfold raw35929step2 raw35929step1; decide +kernel
      have hl : raw35929step1Labels = labelEmbedding7 ∘ raw35929step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35929step1 raw35929step1Labels raw35929step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw35930 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35930step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35930 raw35930Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw35930 raw35930Labels = mixedMoment B raw35930step0 raw35930step0Labels := by
      have ha : raw35930step0 = (fun i j => raw35930 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35930step0 raw35930; decide +kernel
      have hl : raw35930step0Labels = raw35930Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35930 raw35930Labels permutation152 permutation6
    mixedMoment B raw35930step0 raw35930step0Labels = mixedMoment B raw35930step1 raw35930step1Labels := by
      have ha : raw35930step1 = raw35930step0 := by apply Matrix.ext; unfold raw35930step1 raw35930step0; decide +kernel
      have hl : raw35930step0Labels = labelEmbedding9 ∘ raw35930step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35930step0 raw35930step0Labels raw35930step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw35931 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw35931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35931 raw35931Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw35931 raw35931Labels = mixedMoment B raw35931step0 raw35931step0Labels := by
      have ha : raw35931step0 = (fun i j => raw35931 (permutation660 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35931step0 raw35931; decide +kernel
      have hl : raw35931step0Labels = raw35931Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35931 raw35931Labels permutation660 permutation2
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw35932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 4, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 4, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35932step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35932step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35932step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35932step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35932 raw35932Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw35932 raw35932Labels = mixedMoment B raw35932step0 raw35932step0Labels := by
      have hz : ∀ j, raw35932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35932step0 = (fun i j => raw35932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35932step0 raw35932; decide +kernel
      have hl : raw35932step0Labels = raw35932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35932 raw35932Labels permutation346 hz
    mixedMoment B raw35932step0 raw35932step0Labels = mixedMoment B raw35932step1 raw35932step1Labels := by
      have ha : raw35932step1 = (fun i j => raw35932step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35932step1 raw35932step0; decide +kernel
      have hl : raw35932step1Labels = raw35932step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35932step0 raw35932step0Labels permutation56 permutation5
    mixedMoment B raw35932step1 raw35932step1Labels = mixedMoment B raw35932step2 raw35932step2Labels := by
      have ha : raw35932step2 = -raw35932step1 := by apply Matrix.ext; change ∀ i j, raw35932step2 i j = -(raw35932step1 i j); unfold raw35932step2 raw35932step1; decide +kernel
      have hl : raw35932step2Labels = raw35932step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35932step2 raw35932step2Labels = mixedMoment B raw35932step3 raw35932step3Labels := by
      have ha : raw35932step3 = raw35932step2 := by apply Matrix.ext; unfold raw35932step3 raw35932step2; decide +kernel
      have hl : raw35932step2Labels = labelEmbedding8 ∘ raw35932step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35932step2 raw35932step2Labels raw35932step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw35933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35933step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35933step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35933step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35933step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35933 raw35933Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw35933 raw35933Labels = mixedMoment B raw35933step0 raw35933step0Labels := by
      have ha : raw35933step0 = (fun i j => raw35933 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35933step0 raw35933; decide +kernel
      have hl : raw35933step0Labels = raw35933Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35933 raw35933Labels permutation289 permutation5
    mixedMoment B raw35933step0 raw35933step0Labels = mixedMoment B raw35933step1 raw35933step1Labels := by
      have ha : raw35933step1 = -raw35933step0 := by apply Matrix.ext; change ∀ i j, raw35933step1 i j = -(raw35933step0 i j); unfold raw35933step1 raw35933step0; decide +kernel
      have hl : raw35933step1Labels = raw35933step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35933step1 raw35933step1Labels = mixedMoment B raw35933step2 raw35933step2Labels := by
      have ha : raw35933step2 = raw35933step1 := by apply Matrix.ext; unfold raw35933step2 raw35933step1; decide +kernel
      have hl : raw35933step1Labels = labelEmbedding8 ∘ raw35933step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35933step1 raw35933step1Labels raw35933step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

def raw35934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw35934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35934step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35934step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35934step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35934step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35934 raw35934Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw35934 raw35934Labels = mixedMoment B raw35934step0 raw35934step0Labels := by
      have hz : ∀ j, raw35934 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35934step0 = (fun i j => raw35934 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35934step0 raw35934; decide +kernel
      have hl : raw35934step0Labels = raw35934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35934 raw35934Labels permutation520 hz
    mixedMoment B raw35934step0 raw35934step0Labels = mixedMoment B raw35934step1 raw35934step1Labels := by
      have hz : ∀ j, raw35934step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35934step1 = (fun i j => raw35934step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35934step1 raw35934step0; decide +kernel
      have hl : raw35934step1Labels = raw35934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35934step0 raw35934step0Labels permutation80 hz
    mixedMoment B raw35934step1 raw35934step1Labels = mixedMoment B raw35934step2 raw35934step2Labels := by
      have ha : raw35934step2 = (fun i j => raw35934step1 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35934step2 raw35934step1; decide +kernel
      have hl : raw35934step2Labels = raw35934step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35934step1 raw35934step1Labels permutation14 permutation5
    mixedMoment B raw35934step2 raw35934step2Labels = mixedMoment B raw35934step3 raw35934step3Labels := by
      have ha : raw35934step3 = -raw35934step2 := by apply Matrix.ext; change ∀ i j, raw35934step3 i j = -(raw35934step2 i j); unfold raw35934step3 raw35934step2; decide +kernel
      have hl : raw35934step3Labels = raw35934step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35934step3 raw35934step3Labels = mixedMoment B raw35934step4 raw35934step4Labels := by
      have ha : raw35934step4 = raw35934step3 := by apply Matrix.ext; unfold raw35934step4 raw35934step3; decide +kernel
      have hl : raw35934step3Labels = labelEmbedding8 ∘ raw35934step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35934step3 raw35934step3Labels raw35934step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw35935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw35935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw35935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35935step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw35935step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35935step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw35935step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35935 raw35935Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw35935 raw35935Labels = mixedMoment B raw35935step0 raw35935step0Labels := by
      have hz : ∀ j, raw35935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35935step0 = (fun i j => raw35935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35935step0 raw35935; decide +kernel
      have hl : raw35935step0Labels = raw35935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35935 raw35935Labels permutation346 hz
    mixedMoment B raw35935step0 raw35935step0Labels = mixedMoment B raw35935step1 raw35935step1Labels := by
      have ha : raw35935step1 = (fun i j => raw35935step0 (permutation74 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35935step1 raw35935step0; decide +kernel
      have hl : raw35935step1Labels = raw35935step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35935step0 raw35935step0Labels permutation74 permutation5
    mixedMoment B raw35935step1 raw35935step1Labels = mixedMoment B raw35935step2 raw35935step2Labels := by
      have ha : raw35935step2 = -raw35935step1 := by apply Matrix.ext; change ∀ i j, raw35935step2 i j = -(raw35935step1 i j); unfold raw35935step2 raw35935step1; decide +kernel
      have hl : raw35935step2Labels = raw35935step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35935step2 raw35935step2Labels = mixedMoment B raw35935step3 raw35935step3Labels := by
      have ha : raw35935step3 = raw35935step2 := by apply Matrix.ext; unfold raw35935step3 raw35935step2; decide +kernel
      have hl : raw35935step2Labels = labelEmbedding8 ∘ raw35935step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35935step2 raw35935step2Labels raw35935step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw35936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35936step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35936step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35936step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35936step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35936 raw35936Labels = mixedMoment B node4379 node4379Labels := by
  calc
    mixedMoment B raw35936 raw35936Labels = mixedMoment B raw35936step0 raw35936step0Labels := by
      have ha : raw35936step0 = (fun i j => raw35936 (permutation265 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35936step0 raw35936; decide +kernel
      have hl : raw35936step0Labels = raw35936Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35936 raw35936Labels permutation265 permutation5
    mixedMoment B raw35936step0 raw35936step0Labels = mixedMoment B raw35936step1 raw35936step1Labels := by
      have ha : raw35936step1 = -raw35936step0 := by apply Matrix.ext; change ∀ i j, raw35936step1 i j = -(raw35936step0 i j); unfold raw35936step1 raw35936step0; decide +kernel
      have hl : raw35936step1Labels = raw35936step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35936step1 raw35936step1Labels = mixedMoment B raw35936step2 raw35936step2Labels := by
      have ha : raw35936step2 = raw35936step1 := by apply Matrix.ext; unfold raw35936step2 raw35936step1; decide +kernel
      have hl : raw35936step1Labels = labelEmbedding8 ∘ raw35936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35936step1 raw35936step1Labels raw35936step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4379 node4379Labels := by rfl

def raw35937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw35937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35937step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35937step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35937step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35937step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35937 raw35937Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw35937 raw35937Labels = mixedMoment B raw35937step0 raw35937step0Labels := by
      have hz : ∀ j, raw35937 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35937step0 = (fun i j => raw35937 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35937step0 raw35937; decide +kernel
      have hl : raw35937step0Labels = raw35937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35937 raw35937Labels permutation520 hz
    mixedMoment B raw35937step0 raw35937step0Labels = mixedMoment B raw35937step1 raw35937step1Labels := by
      have ha : raw35937step1 = (fun i j => raw35937step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35937step1 raw35937step0; decide +kernel
      have hl : raw35937step1Labels = raw35937step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35937step0 raw35937step0Labels permutation56 permutation5
    mixedMoment B raw35937step1 raw35937step1Labels = mixedMoment B raw35937step2 raw35937step2Labels := by
      have ha : raw35937step2 = -raw35937step1 := by apply Matrix.ext; change ∀ i j, raw35937step2 i j = -(raw35937step1 i j); unfold raw35937step2 raw35937step1; decide +kernel
      have hl : raw35937step2Labels = raw35937step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35937step2 raw35937step2Labels = mixedMoment B raw35937step3 raw35937step3Labels := by
      have ha : raw35937step3 = raw35937step2 := by apply Matrix.ext; unfold raw35937step3 raw35937step2; decide +kernel
      have hl : raw35937step2Labels = labelEmbedding8 ∘ raw35937step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35937step2 raw35937step2Labels raw35937step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw35938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35938step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35938step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35938step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35938step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35938 raw35938Labels = mixedMoment B node4381 node4381Labels := by
  calc
    mixedMoment B raw35938 raw35938Labels = mixedMoment B raw35938step0 raw35938step0Labels := by
      have hz : ∀ j, raw35938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35938step0 = (fun i j => raw35938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35938step0 raw35938; decide +kernel
      have hl : raw35938step0Labels = raw35938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35938 raw35938Labels permutation346 hz
    mixedMoment B raw35938step0 raw35938step0Labels = mixedMoment B raw35938step1 raw35938step1Labels := by
      have ha : raw35938step1 = (fun i j => raw35938step0 (permutation59 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35938step1 raw35938step0; decide +kernel
      have hl : raw35938step1Labels = raw35938step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35938step0 raw35938step0Labels permutation59 permutation5
    mixedMoment B raw35938step1 raw35938step1Labels = mixedMoment B raw35938step2 raw35938step2Labels := by
      have ha : raw35938step2 = -raw35938step1 := by apply Matrix.ext; change ∀ i j, raw35938step2 i j = -(raw35938step1 i j); unfold raw35938step2 raw35938step1; decide +kernel
      have hl : raw35938step2Labels = raw35938step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35938step2 raw35938step2Labels = mixedMoment B raw35938step3 raw35938step3Labels := by
      have ha : raw35938step3 = raw35938step2 := by apply Matrix.ext; unfold raw35938step3 raw35938step2; decide +kernel
      have hl : raw35938step2Labels = labelEmbedding8 ∘ raw35938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35938step2 raw35938step2Labels raw35938step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4381 node4381Labels := by rfl

def raw35939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35939step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35939step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35939step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35939 raw35939Labels = mixedMoment B node5046 node5046Labels := by
  calc
    mixedMoment B raw35939 raw35939Labels = mixedMoment B raw35939step0 raw35939step0Labels := by
      have ha : raw35939step0 = (fun i j => raw35939 (permutation292 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35939step0 raw35939; decide +kernel
      have hl : raw35939step0Labels = raw35939Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35939 raw35939Labels permutation292 permutation5
    mixedMoment B raw35939step0 raw35939step0Labels = mixedMoment B raw35939step1 raw35939step1Labels := by
      have ha : raw35939step1 = -raw35939step0 := by apply Matrix.ext; change ∀ i j, raw35939step1 i j = -(raw35939step0 i j); unfold raw35939step1 raw35939step0; decide +kernel
      have hl : raw35939step1Labels = raw35939step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35939step1 raw35939step1Labels = mixedMoment B raw35939step2 raw35939step2Labels := by
      have ha : raw35939step2 = raw35939step1 := by apply Matrix.ext; unfold raw35939step2 raw35939step1; decide +kernel
      have hl : raw35939step1Labels = labelEmbedding8 ∘ raw35939step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35939step1 raw35939step1Labels raw35939step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5046 node5046Labels := by rfl

def raw35940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw35940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35940step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw35940step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35940step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw35940step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35940step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw35940step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35940 raw35940Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw35940 raw35940Labels = mixedMoment B raw35940step0 raw35940step0Labels := by
      have hz : ∀ j, raw35940 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35940step0 = (fun i j => raw35940 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35940step0 raw35940; decide +kernel
      have hl : raw35940step0Labels = raw35940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35940 raw35940Labels permutation520 hz
    mixedMoment B raw35940step0 raw35940step0Labels = mixedMoment B raw35940step1 raw35940step1Labels := by
      have hz : ∀ j, raw35940step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35940step1 = (fun i j => raw35940step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35940step1 raw35940step0; decide +kernel
      have hl : raw35940step1Labels = raw35940step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35940step0 raw35940step0Labels permutation80 hz
    mixedMoment B raw35940step1 raw35940step1Labels = mixedMoment B raw35940step2 raw35940step2Labels := by
      have ha : raw35940step2 = (fun i j => raw35940step1 (permutation15 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35940step2 raw35940step1; decide +kernel
      have hl : raw35940step2Labels = raw35940step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35940step1 raw35940step1Labels permutation15 permutation5
    mixedMoment B raw35940step2 raw35940step2Labels = mixedMoment B raw35940step3 raw35940step3Labels := by
      have ha : raw35940step3 = -raw35940step2 := by apply Matrix.ext; change ∀ i j, raw35940step3 i j = -(raw35940step2 i j); unfold raw35940step3 raw35940step2; decide +kernel
      have hl : raw35940step3Labels = raw35940step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35940step3 raw35940step3Labels = mixedMoment B raw35940step4 raw35940step4Labels := by
      have ha : raw35940step4 = raw35940step3 := by apply Matrix.ext; unfold raw35940step4 raw35940step3; decide +kernel
      have hl : raw35940step3Labels = labelEmbedding8 ∘ raw35940step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35940step3 raw35940step3Labels raw35940step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw35941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw35941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw35941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35941step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35941step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35941step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35941step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35941 raw35941Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35941 raw35941Labels = mixedMoment B raw35941step0 raw35941step0Labels := by
      have hz : ∀ j, raw35941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35941step0 = (fun i j => raw35941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35941step0 raw35941; decide +kernel
      have hl : raw35941step0Labels = raw35941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35941 raw35941Labels permutation346 hz
    mixedMoment B raw35941step0 raw35941step0Labels = mixedMoment B raw35941step1 raw35941step1Labels := by
      have ha : raw35941step1 = (fun i j => raw35941step0 (permutation61 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35941step1 raw35941step0; decide +kernel
      have hl : raw35941step1Labels = raw35941step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35941step0 raw35941step0Labels permutation61 permutation5
    mixedMoment B raw35941step1 raw35941step1Labels = mixedMoment B raw35941step2 raw35941step2Labels := by
      have ha : raw35941step2 = -raw35941step1 := by apply Matrix.ext; change ∀ i j, raw35941step2 i j = -(raw35941step1 i j); unfold raw35941step2 raw35941step1; decide +kernel
      have hl : raw35941step2Labels = raw35941step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35941step2 raw35941step2Labels = mixedMoment B raw35941step3 raw35941step3Labels := by
      have ha : raw35941step3 = raw35941step2 := by apply Matrix.ext; unfold raw35941step3 raw35941step2; decide +kernel
      have hl : raw35941step2Labels = labelEmbedding8 ∘ raw35941step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35941step2 raw35941step2Labels raw35941step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw35942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw35942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw35942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw35942step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw35942step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35942step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw35942step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35942 raw35942Labels = mixedMoment B node4380 node4380Labels := by
  calc
    mixedMoment B raw35942 raw35942Labels = mixedMoment B raw35942step0 raw35942step0Labels := by
      have hz : ∀ j, raw35942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35942step0 = (fun i j => raw35942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35942step0 raw35942; decide +kernel
      have hl : raw35942step0Labels = raw35942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35942 raw35942Labels permutation346 hz
    mixedMoment B raw35942step0 raw35942step0Labels = mixedMoment B raw35942step1 raw35942step1Labels := by
      have ha : raw35942step1 = (fun i j => raw35942step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35942step1 raw35942step0; decide +kernel
      have hl : raw35942step1Labels = raw35942step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35942step0 raw35942step0Labels permutation56 permutation5
    mixedMoment B raw35942step1 raw35942step1Labels = mixedMoment B raw35942step2 raw35942step2Labels := by
      have ha : raw35942step2 = -raw35942step1 := by apply Matrix.ext; change ∀ i j, raw35942step2 i j = -(raw35942step1 i j); unfold raw35942step2 raw35942step1; decide +kernel
      have hl : raw35942step2Labels = raw35942step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35942step2 raw35942step2Labels = mixedMoment B raw35942step3 raw35942step3Labels := by
      have ha : raw35942step3 = raw35942step2 := by apply Matrix.ext; unfold raw35942step3 raw35942step2; decide +kernel
      have hl : raw35942step2Labels = labelEmbedding8 ∘ raw35942step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35942step2 raw35942step2Labels raw35942step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4380 node4380Labels := by rfl

def raw35943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw35943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35943step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35943step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35943step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35943step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35943 raw35943Labels = mixedMoment B node5028 node5028Labels := by
  calc
    mixedMoment B raw35943 raw35943Labels = mixedMoment B raw35943step0 raw35943step0Labels := by
      have ha : raw35943step0 = (fun i j => raw35943 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35943step0 raw35943; decide +kernel
      have hl : raw35943step0Labels = raw35943Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35943 raw35943Labels permutation663 permutation3
    mixedMoment B raw35943step0 raw35943step0Labels = mixedMoment B raw35943step1 raw35943step1Labels := by
      have ha : raw35943step1 = -raw35943step0 := by apply Matrix.ext; change ∀ i j, raw35943step1 i j = -(raw35943step0 i j); unfold raw35943step1 raw35943step0; decide +kernel
      have hl : raw35943step1Labels = raw35943step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35943step1 raw35943step1Labels = mixedMoment B raw35943step2 raw35943step2Labels := by
      have ha : raw35943step2 = raw35943step1 := by apply Matrix.ext; unfold raw35943step2 raw35943step1; decide +kernel
      have hl : raw35943step1Labels = labelEmbedding6 ∘ raw35943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35943step1 raw35943step1Labels raw35943step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5028 node5028Labels := by rfl

def raw35944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw35944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw35944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![3, -2, -1]]
def raw35944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35944step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35944step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw35944step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35944step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw35944step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35944 raw35944Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw35944 raw35944Labels = mixedMoment B raw35944step0 raw35944step0Labels := by
      have hz : ∀ j, raw35944 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35944step0 = (fun i j => raw35944 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35944step0 raw35944; decide +kernel
      have hl : raw35944step0Labels = raw35944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35944 raw35944Labels permutation520 hz
    mixedMoment B raw35944step0 raw35944step0Labels = mixedMoment B raw35944step1 raw35944step1Labels := by
      have hz : ∀ j, raw35944step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35944step1 = (fun i j => raw35944step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35944step1 raw35944step0; decide +kernel
      have hl : raw35944step1Labels = raw35944step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35944step0 raw35944step0Labels permutation80 hz
    mixedMoment B raw35944step1 raw35944step1Labels = mixedMoment B raw35944step2 raw35944step2Labels := by
      have ha : raw35944step2 = (fun i j => raw35944step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35944step2 raw35944step1; decide +kernel
      have hl : raw35944step2Labels = raw35944step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35944step1 raw35944step1Labels permutation30 permutation3
    mixedMoment B raw35944step2 raw35944step2Labels = mixedMoment B raw35944step3 raw35944step3Labels := by
      have ha : raw35944step3 = -raw35944step2 := by apply Matrix.ext; change ∀ i j, raw35944step3 i j = -(raw35944step2 i j); unfold raw35944step3 raw35944step2; decide +kernel
      have hl : raw35944step3Labels = raw35944step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35944step3 raw35944step3Labels = mixedMoment B raw35944step4 raw35944step4Labels := by
      have ha : raw35944step4 = raw35944step3 := by apply Matrix.ext; unfold raw35944step4 raw35944step3; decide +kernel
      have hl : raw35944step3Labels = labelEmbedding6 ∘ raw35944step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35944step3 raw35944step3Labels raw35944step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw35945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35945 raw35945Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw35945 raw35945Labels = mixedMoment B raw35945step0 raw35945step0Labels := by
      have hz : ∀ j, raw35945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35945step0 = (fun i j => raw35945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35945step0 raw35945; decide +kernel
      have hl : raw35945step0Labels = raw35945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35945 raw35945Labels permutation346 hz
    mixedMoment B raw35945step0 raw35945step0Labels = mixedMoment B raw35945step1 raw35945step1Labels := by
      have ha : raw35945step1 = (fun i j => raw35945step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35945step1 raw35945step0; decide +kernel
      have hl : raw35945step1Labels = raw35945step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35945step0 raw35945step0Labels permutation56 permutation2
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw35946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35946step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35946step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35946step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35946 raw35946Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw35946 raw35946Labels = mixedMoment B raw35946step0 raw35946step0Labels := by
      have ha : raw35946step0 = (fun i j => raw35946 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35946step0 raw35946; decide +kernel
      have hl : raw35946step0Labels = raw35946Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35946 raw35946Labels permutation265 permutation7
    mixedMoment B raw35946step0 raw35946step0Labels = mixedMoment B raw35946step1 raw35946step1Labels := by
      have ha : raw35946step1 = -raw35946step0 := by apply Matrix.ext; change ∀ i j, raw35946step1 i j = -(raw35946step0 i j); unfold raw35946step1 raw35946step0; decide +kernel
      have hl : raw35946step1Labels = raw35946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35946step1 raw35946step1Labels = mixedMoment B raw35946step2 raw35946step2Labels := by
      have ha : raw35946step2 = raw35946step1 := by apply Matrix.ext; unfold raw35946step2 raw35946step1; decide +kernel
      have hl : raw35946step1Labels = labelEmbedding10 ∘ raw35946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35946step1 raw35946step1Labels raw35946step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw35947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35947step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35947step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35947step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35947step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35947 raw35947Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw35947 raw35947Labels = mixedMoment B raw35947step0 raw35947step0Labels := by
      have hz : ∀ j, raw35947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35947step0 = (fun i j => raw35947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35947step0 raw35947; decide +kernel
      have hl : raw35947step0Labels = raw35947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35947 raw35947Labels permutation346 hz
    mixedMoment B raw35947step0 raw35947step0Labels = mixedMoment B raw35947step1 raw35947step1Labels := by
      have ha : raw35947step1 = (fun i j => raw35947step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35947step1 raw35947step0; decide +kernel
      have hl : raw35947step1Labels = raw35947step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35947step0 raw35947step0Labels permutation56 permutation7
    mixedMoment B raw35947step1 raw35947step1Labels = mixedMoment B raw35947step2 raw35947step2Labels := by
      have ha : raw35947step2 = -raw35947step1 := by apply Matrix.ext; change ∀ i j, raw35947step2 i j = -(raw35947step1 i j); unfold raw35947step2 raw35947step1; decide +kernel
      have hl : raw35947step2Labels = raw35947step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35947step2 raw35947step2Labels = mixedMoment B raw35947step3 raw35947step3Labels := by
      have ha : raw35947step3 = raw35947step2 := by apply Matrix.ext; unfold raw35947step3 raw35947step2; decide +kernel
      have hl : raw35947step2Labels = labelEmbedding10 ∘ raw35947step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35947step2 raw35947step2Labels raw35947step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw35948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35948step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35948step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35948step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35948 raw35948Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw35948 raw35948Labels = mixedMoment B raw35948step0 raw35948step0Labels := by
      have hz : ∀ j, raw35948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35948step0 = (fun i j => raw35948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35948step0 raw35948; decide +kernel
      have hl : raw35948step0Labels = raw35948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35948 raw35948Labels permutation346 hz
    mixedMoment B raw35948step0 raw35948step0Labels = mixedMoment B raw35948step1 raw35948step1Labels := by
      have ha : raw35948step1 = (fun i j => raw35948step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35948step1 raw35948step0; decide +kernel
      have hl : raw35948step1Labels = raw35948step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35948step0 raw35948step0Labels permutation58 permutation7
    mixedMoment B raw35948step1 raw35948step1Labels = mixedMoment B raw35948step2 raw35948step2Labels := by
      have ha : raw35948step2 = -raw35948step1 := by apply Matrix.ext; change ∀ i j, raw35948step2 i j = -(raw35948step1 i j); unfold raw35948step2 raw35948step1; decide +kernel
      have hl : raw35948step2Labels = raw35948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35948step2 raw35948step2Labels = mixedMoment B raw35948step3 raw35948step3Labels := by
      have ha : raw35948step3 = raw35948step2 := by apply Matrix.ext; unfold raw35948step3 raw35948step2; decide +kernel
      have hl : raw35948step2Labels = labelEmbedding10 ∘ raw35948step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35948step2 raw35948step2Labels raw35948step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw35949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35949step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35949step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35949step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35949step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35949 raw35949Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw35949 raw35949Labels = mixedMoment B raw35949step0 raw35949step0Labels := by
      have hz : ∀ j, raw35949 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35949step0 = (fun i j => raw35949 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35949step0 raw35949; decide +kernel
      have hl : raw35949step0Labels = raw35949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35949 raw35949Labels permutation346 hz
    mixedMoment B raw35949step0 raw35949step0Labels = mixedMoment B raw35949step1 raw35949step1Labels := by
      have ha : raw35949step1 = (fun i j => raw35949step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35949step1 raw35949step0; decide +kernel
      have hl : raw35949step1Labels = raw35949step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35949step0 raw35949step0Labels permutation56 permutation7
    mixedMoment B raw35949step1 raw35949step1Labels = mixedMoment B raw35949step2 raw35949step2Labels := by
      have ha : raw35949step2 = -raw35949step1 := by apply Matrix.ext; change ∀ i j, raw35949step2 i j = -(raw35949step1 i j); unfold raw35949step2 raw35949step1; decide +kernel
      have hl : raw35949step2Labels = raw35949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35949step2 raw35949step2Labels = mixedMoment B raw35949step3 raw35949step3Labels := by
      have ha : raw35949step3 = raw35949step2 := by apply Matrix.ext; unfold raw35949step3 raw35949step2; decide +kernel
      have hl : raw35949step2Labels = labelEmbedding10 ∘ raw35949step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35949step2 raw35949step2Labels raw35949step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw35950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35950step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35950step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35950 raw35950Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw35950 raw35950Labels = mixedMoment B raw35950step0 raw35950step0Labels := by
      have hz : ∀ j, raw35950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35950step0 = (fun i j => raw35950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35950step0 raw35950; decide +kernel
      have hl : raw35950step0Labels = raw35950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35950 raw35950Labels permutation346 hz
    mixedMoment B raw35950step0 raw35950step0Labels = mixedMoment B raw35950step1 raw35950step1Labels := by
      have ha : raw35950step1 = (fun i j => raw35950step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35950step1 raw35950step0; decide +kernel
      have hl : raw35950step1Labels = raw35950step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35950step0 raw35950step0Labels permutation32 permutation3
    mixedMoment B raw35950step1 raw35950step1Labels = mixedMoment B raw35950step2 raw35950step2Labels := by
      have ha : raw35950step2 = raw35950step1 := by apply Matrix.ext; unfold raw35950step2 raw35950step1; decide +kernel
      have hl : raw35950step1Labels = labelEmbedding6 ∘ raw35950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35950step1 raw35950step1Labels raw35950step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw35951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw35951step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw35951step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35951step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw35951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35951 raw35951Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw35951 raw35951Labels = mixedMoment B raw35951step0 raw35951step0Labels := by
      have ha : raw35951step0 = (fun i j => raw35951 (permutation293 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35951step0 raw35951; decide +kernel
      have hl : raw35951step0Labels = raw35951Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35951 raw35951Labels permutation293 permutation6
    mixedMoment B raw35951step0 raw35951step0Labels = mixedMoment B raw35951step1 raw35951step1Labels := by
      have ha : raw35951step1 = -raw35951step0 := by apply Matrix.ext; change ∀ i j, raw35951step1 i j = -(raw35951step0 i j); unfold raw35951step1 raw35951step0; decide +kernel
      have hl : raw35951step1Labels = raw35951step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35951step1 raw35951step1Labels = mixedMoment B raw35951step2 raw35951step2Labels := by
      have ha : raw35951step2 = raw35951step1 := by apply Matrix.ext; unfold raw35951step2 raw35951step1; decide +kernel
      have hl : raw35951step1Labels = labelEmbedding9 ∘ raw35951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35951step1 raw35951step1Labels raw35951step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw35952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw35952step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35952step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35952step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35952 raw35952Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw35952 raw35952Labels = mixedMoment B raw35952step0 raw35952step0Labels := by
      have hz : ∀ j, raw35952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35952step0 = (fun i j => raw35952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35952step0 raw35952; decide +kernel
      have hl : raw35952step0Labels = raw35952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35952 raw35952Labels permutation346 hz
    mixedMoment B raw35952step0 raw35952step0Labels = mixedMoment B raw35952step1 raw35952step1Labels := by
      have ha : raw35952step1 = (fun i j => raw35952step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35952step1 raw35952step0; decide +kernel
      have hl : raw35952step1Labels = raw35952step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35952step0 raw35952step0Labels permutation61 permutation6
    mixedMoment B raw35952step1 raw35952step1Labels = mixedMoment B raw35952step2 raw35952step2Labels := by
      have ha : raw35952step2 = -raw35952step1 := by apply Matrix.ext; change ∀ i j, raw35952step2 i j = -(raw35952step1 i j); unfold raw35952step2 raw35952step1; decide +kernel
      have hl : raw35952step2Labels = raw35952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35952step2 raw35952step2Labels = mixedMoment B raw35952step3 raw35952step3Labels := by
      have ha : raw35952step3 = raw35952step2 := by apply Matrix.ext; unfold raw35952step3 raw35952step2; decide +kernel
      have hl : raw35952step2Labels = labelEmbedding9 ∘ raw35952step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35952step2 raw35952step2Labels raw35952step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw35953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw35953step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35953step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35953step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35953step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35953 raw35953Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw35953 raw35953Labels = mixedMoment B raw35953step0 raw35953step0Labels := by
      have hz : ∀ j, raw35953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35953step0 = (fun i j => raw35953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35953step0 raw35953; decide +kernel
      have hl : raw35953step0Labels = raw35953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35953 raw35953Labels permutation346 hz
    mixedMoment B raw35953step0 raw35953step0Labels = mixedMoment B raw35953step1 raw35953step1Labels := by
      have ha : raw35953step1 = (fun i j => raw35953step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35953step1 raw35953step0; decide +kernel
      have hl : raw35953step1Labels = raw35953step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35953step0 raw35953step0Labels permutation60 permutation6
    mixedMoment B raw35953step1 raw35953step1Labels = mixedMoment B raw35953step2 raw35953step2Labels := by
      have ha : raw35953step2 = -raw35953step1 := by apply Matrix.ext; change ∀ i j, raw35953step2 i j = -(raw35953step1 i j); unfold raw35953step2 raw35953step1; decide +kernel
      have hl : raw35953step2Labels = raw35953step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35953step2 raw35953step2Labels = mixedMoment B raw35953step3 raw35953step3Labels := by
      have ha : raw35953step3 = raw35953step2 := by apply Matrix.ext; unfold raw35953step3 raw35953step2; decide +kernel
      have hl : raw35953step2Labels = labelEmbedding9 ∘ raw35953step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35953step2 raw35953step2Labels raw35953step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw35954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw35954step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw35954step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35954step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw35954step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35954 raw35954Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw35954 raw35954Labels = mixedMoment B raw35954step0 raw35954step0Labels := by
      have hz : ∀ j, raw35954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35954step0 = (fun i j => raw35954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35954step0 raw35954; decide +kernel
      have hl : raw35954step0Labels = raw35954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35954 raw35954Labels permutation346 hz
    mixedMoment B raw35954step0 raw35954step0Labels = mixedMoment B raw35954step1 raw35954step1Labels := by
      have ha : raw35954step1 = (fun i j => raw35954step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35954step1 raw35954step0; decide +kernel
      have hl : raw35954step1Labels = raw35954step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35954step0 raw35954step0Labels permutation56 permutation6
    mixedMoment B raw35954step1 raw35954step1Labels = mixedMoment B raw35954step2 raw35954step2Labels := by
      have ha : raw35954step2 = -raw35954step1 := by apply Matrix.ext; change ∀ i j, raw35954step2 i j = -(raw35954step1 i j); unfold raw35954step2 raw35954step1; decide +kernel
      have hl : raw35954step2Labels = raw35954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35954step2 raw35954step2Labels = mixedMoment B raw35954step3 raw35954step3Labels := by
      have ha : raw35954step3 = raw35954step2 := by apply Matrix.ext; unfold raw35954step3 raw35954step2; decide +kernel
      have hl : raw35954step2Labels = labelEmbedding9 ∘ raw35954step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35954step2 raw35954step2Labels raw35954step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw35955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35955step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35955step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35955 raw35955Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw35955 raw35955Labels = mixedMoment B raw35955step0 raw35955step0Labels := by
      have ha : raw35955step0 = (fun i j => raw35955 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35955step0 raw35955; decide +kernel
      have hl : raw35955step0Labels = raw35955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35955 raw35955Labels permutation160 permutation3
    mixedMoment B raw35955step0 raw35955step0Labels = mixedMoment B raw35955step1 raw35955step1Labels := by
      have ha : raw35955step1 = raw35955step0 := by apply Matrix.ext; unfold raw35955step1 raw35955step0; decide +kernel
      have hl : raw35955step0Labels = labelEmbedding6 ∘ raw35955step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35955step0 raw35955step0Labels raw35955step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4696 node4696Labels := by rfl

def raw35956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35956 raw35956Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw35956 raw35956Labels = mixedMoment B raw35956step0 raw35956step0Labels := by
      have ha : raw35956step0 = (fun i j => raw35956 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35956step0 raw35956; decide +kernel
      have hl : raw35956step0Labels = raw35956Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35956 raw35956Labels permutation265 permutation2
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw35957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35957step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35957step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35957 raw35957Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw35957 raw35957Labels = mixedMoment B raw35957step0 raw35957step0Labels := by
      have ha : raw35957step0 = (fun i j => raw35957 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35957step0 raw35957; decide +kernel
      have hl : raw35957step0Labels = raw35957Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35957 raw35957Labels permutation265 permutation7
    mixedMoment B raw35957step0 raw35957step0Labels = mixedMoment B raw35957step1 raw35957step1Labels := by
      have ha : raw35957step1 = -raw35957step0 := by apply Matrix.ext; change ∀ i j, raw35957step1 i j = -(raw35957step0 i j); unfold raw35957step1 raw35957step0; decide +kernel
      have hl : raw35957step1Labels = raw35957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35957step1 raw35957step1Labels = mixedMoment B raw35957step2 raw35957step2Labels := by
      have ha : raw35957step2 = raw35957step1 := by apply Matrix.ext; unfold raw35957step2 raw35957step1; decide +kernel
      have hl : raw35957step1Labels = labelEmbedding10 ∘ raw35957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35957step1 raw35957step1Labels raw35957step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw35958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35958step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35958step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35958step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35958 raw35958Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw35958 raw35958Labels = mixedMoment B raw35958step0 raw35958step0Labels := by
      have ha : raw35958step0 = (fun i j => raw35958 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35958step0 raw35958; decide +kernel
      have hl : raw35958step0Labels = raw35958Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35958 raw35958Labels permutation267 permutation7
    mixedMoment B raw35958step0 raw35958step0Labels = mixedMoment B raw35958step1 raw35958step1Labels := by
      have ha : raw35958step1 = -raw35958step0 := by apply Matrix.ext; change ∀ i j, raw35958step1 i j = -(raw35958step0 i j); unfold raw35958step1 raw35958step0; decide +kernel
      have hl : raw35958step1Labels = raw35958step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35958step1 raw35958step1Labels = mixedMoment B raw35958step2 raw35958step2Labels := by
      have ha : raw35958step2 = raw35958step1 := by apply Matrix.ext; unfold raw35958step2 raw35958step1; decide +kernel
      have hl : raw35958step1Labels = labelEmbedding10 ∘ raw35958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35958step1 raw35958step1Labels raw35958step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw35959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35959step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35959step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35959step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35959 raw35959Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw35959 raw35959Labels = mixedMoment B raw35959step0 raw35959step0Labels := by
      have ha : raw35959step0 = (fun i j => raw35959 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35959step0 raw35959; decide +kernel
      have hl : raw35959step0Labels = raw35959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35959 raw35959Labels permutation265 permutation7
    mixedMoment B raw35959step0 raw35959step0Labels = mixedMoment B raw35959step1 raw35959step1Labels := by
      have ha : raw35959step1 = -raw35959step0 := by apply Matrix.ext; change ∀ i j, raw35959step1 i j = -(raw35959step0 i j); unfold raw35959step1 raw35959step0; decide +kernel
      have hl : raw35959step1Labels = raw35959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35959step1 raw35959step1Labels = mixedMoment B raw35959step2 raw35959step2Labels := by
      have ha : raw35959step2 = raw35959step1 := by apply Matrix.ext; unfold raw35959step2 raw35959step1; decide +kernel
      have hl : raw35959step1Labels = labelEmbedding10 ∘ raw35959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35959step1 raw35959step1Labels raw35959step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

def raw35960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35960step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35960step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35960 raw35960Labels = mixedMoment B node4701 node4701Labels := by
  calc
    mixedMoment B raw35960 raw35960Labels = mixedMoment B raw35960step0 raw35960step0Labels := by
      have hz : ∀ j, raw35960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35960step0 = (fun i j => raw35960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35960step0 raw35960; decide +kernel
      have hl : raw35960step0Labels = raw35960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35960 raw35960Labels permutation346 hz
    mixedMoment B raw35960step0 raw35960step0Labels = mixedMoment B raw35960step1 raw35960step1Labels := by
      have ha : raw35960step1 = (fun i j => raw35960step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35960step1 raw35960step0; decide +kernel
      have hl : raw35960step1Labels = raw35960step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35960step0 raw35960step0Labels permutation34 permutation3
    mixedMoment B raw35960step1 raw35960step1Labels = mixedMoment B raw35960step2 raw35960step2Labels := by
      have ha : raw35960step2 = raw35960step1 := by apply Matrix.ext; unfold raw35960step2 raw35960step1; decide +kernel
      have hl : raw35960step1Labels = labelEmbedding6 ∘ raw35960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35960step1 raw35960step1Labels raw35960step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4701 node4701Labels := by rfl

def raw35961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35961step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35961 raw35961Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw35961 raw35961Labels = mixedMoment B raw35961step0 raw35961step0Labels := by
      have hz : ∀ j, raw35961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35961step0 = (fun i j => raw35961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35961step0 raw35961; decide +kernel
      have hl : raw35961step0Labels = raw35961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35961 raw35961Labels permutation346 hz
    mixedMoment B raw35961step0 raw35961step0Labels = mixedMoment B raw35961step1 raw35961step1Labels := by
      have ha : raw35961step1 = (fun i j => raw35961step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35961step1 raw35961step0; decide +kernel
      have hl : raw35961step1Labels = raw35961step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35961step0 raw35961step0Labels permutation58 permutation2
    _ = mixedMoment B node4689 node4689Labels := by rfl

def raw35962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35962step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35962step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35962step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35962step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35962 raw35962Labels = mixedMoment B node5217 node5217Labels := by
  calc
    mixedMoment B raw35962 raw35962Labels = mixedMoment B raw35962step0 raw35962step0Labels := by
      have ha : raw35962step0 = (fun i j => raw35962 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35962step0 raw35962; decide +kernel
      have hl : raw35962step0Labels = raw35962Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35962 raw35962Labels permutation267 permutation7
    mixedMoment B raw35962step0 raw35962step0Labels = mixedMoment B raw35962step1 raw35962step1Labels := by
      have ha : raw35962step1 = -raw35962step0 := by apply Matrix.ext; change ∀ i j, raw35962step1 i j = -(raw35962step0 i j); unfold raw35962step1 raw35962step0; decide +kernel
      have hl : raw35962step1Labels = raw35962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35962step1 raw35962step1Labels = mixedMoment B raw35962step2 raw35962step2Labels := by
      have ha : raw35962step2 = raw35962step1 := by apply Matrix.ext; unfold raw35962step2 raw35962step1; decide +kernel
      have hl : raw35962step1Labels = labelEmbedding10 ∘ raw35962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35962step1 raw35962step1Labels raw35962step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5217 node5217Labels := by rfl

def raw35963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35963step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35963step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35963step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35963step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35963step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35963 raw35963Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw35963 raw35963Labels = mixedMoment B raw35963step0 raw35963step0Labels := by
      have hz : ∀ j, raw35963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35963step0 = (fun i j => raw35963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35963step0 raw35963; decide +kernel
      have hl : raw35963step0Labels = raw35963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35963 raw35963Labels permutation346 hz
    mixedMoment B raw35963step0 raw35963step0Labels = mixedMoment B raw35963step1 raw35963step1Labels := by
      have ha : raw35963step1 = (fun i j => raw35963step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35963step1 raw35963step0; decide +kernel
      have hl : raw35963step1Labels = raw35963step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35963step0 raw35963step0Labels permutation58 permutation7
    mixedMoment B raw35963step1 raw35963step1Labels = mixedMoment B raw35963step2 raw35963step2Labels := by
      have ha : raw35963step2 = -raw35963step1 := by apply Matrix.ext; change ∀ i j, raw35963step2 i j = -(raw35963step1 i j); unfold raw35963step2 raw35963step1; decide +kernel
      have hl : raw35963step2Labels = raw35963step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35963step2 raw35963step2Labels = mixedMoment B raw35963step3 raw35963step3Labels := by
      have ha : raw35963step3 = raw35963step2 := by apply Matrix.ext; unfold raw35963step3 raw35963step2; decide +kernel
      have hl : raw35963step2Labels = labelEmbedding10 ∘ raw35963step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35963step2 raw35963step2Labels raw35963step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw35964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35964step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35964step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35964step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35964step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35964step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35964 raw35964Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw35964 raw35964Labels = mixedMoment B raw35964step0 raw35964step0Labels := by
      have hz : ∀ j, raw35964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35964step0 = (fun i j => raw35964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35964step0 raw35964; decide +kernel
      have hl : raw35964step0Labels = raw35964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35964 raw35964Labels permutation346 hz
    mixedMoment B raw35964step0 raw35964step0Labels = mixedMoment B raw35964step1 raw35964step1Labels := by
      have ha : raw35964step1 = (fun i j => raw35964step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35964step1 raw35964step0; decide +kernel
      have hl : raw35964step1Labels = raw35964step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35964step0 raw35964step0Labels permutation59 permutation7
    mixedMoment B raw35964step1 raw35964step1Labels = mixedMoment B raw35964step2 raw35964step2Labels := by
      have ha : raw35964step2 = -raw35964step1 := by apply Matrix.ext; change ∀ i j, raw35964step2 i j = -(raw35964step1 i j); unfold raw35964step2 raw35964step1; decide +kernel
      have hl : raw35964step2Labels = raw35964step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35964step2 raw35964step2Labels = mixedMoment B raw35964step3 raw35964step3Labels := by
      have ha : raw35964step3 = raw35964step2 := by apply Matrix.ext; unfold raw35964step3 raw35964step2; decide +kernel
      have hl : raw35964step2Labels = labelEmbedding10 ∘ raw35964step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35964step2 raw35964step2Labels raw35964step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw35965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35965step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35965step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35965 raw35965Labels = mixedMoment B node4701 node4701Labels := by
  calc
    mixedMoment B raw35965 raw35965Labels = mixedMoment B raw35965step0 raw35965step0Labels := by
      have hz : ∀ j, raw35965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35965step0 = (fun i j => raw35965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35965step0 raw35965; decide +kernel
      have hl : raw35965step0Labels = raw35965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35965 raw35965Labels permutation346 hz
    mixedMoment B raw35965step0 raw35965step0Labels = mixedMoment B raw35965step1 raw35965step1Labels := by
      have ha : raw35965step1 = (fun i j => raw35965step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35965step1 raw35965step0; decide +kernel
      have hl : raw35965step1Labels = raw35965step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35965step0 raw35965step0Labels permutation32 permutation3
    mixedMoment B raw35965step1 raw35965step1Labels = mixedMoment B raw35965step2 raw35965step2Labels := by
      have ha : raw35965step2 = raw35965step1 := by apply Matrix.ext; unfold raw35965step2 raw35965step1; decide +kernel
      have hl : raw35965step1Labels = labelEmbedding6 ∘ raw35965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35965step1 raw35965step1Labels raw35965step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4701 node4701Labels := by rfl

def raw35966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35966 raw35966Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw35966 raw35966Labels = mixedMoment B raw35966step0 raw35966step0Labels := by
      have hz : ∀ j, raw35966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35966step0 = (fun i j => raw35966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35966step0 raw35966; decide +kernel
      have hl : raw35966step0Labels = raw35966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35966 raw35966Labels permutation346 hz
    mixedMoment B raw35966step0 raw35966step0Labels = mixedMoment B raw35966step1 raw35966step1Labels := by
      have ha : raw35966step1 = (fun i j => raw35966step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35966step1 raw35966step0; decide +kernel
      have hl : raw35966step1Labels = raw35966step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35966step0 raw35966step0Labels permutation56 permutation2
    _ = mixedMoment B node4689 node4689Labels := by rfl

def raw35967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35967step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35967step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35967step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35967step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35967 raw35967Labels = mixedMoment B node5217 node5217Labels := by
  calc
    mixedMoment B raw35967 raw35967Labels = mixedMoment B raw35967step0 raw35967step0Labels := by
      have ha : raw35967step0 = (fun i j => raw35967 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35967step0 raw35967; decide +kernel
      have hl : raw35967step0Labels = raw35967Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35967 raw35967Labels permutation265 permutation7
    mixedMoment B raw35967step0 raw35967step0Labels = mixedMoment B raw35967step1 raw35967step1Labels := by
      have ha : raw35967step1 = -raw35967step0 := by apply Matrix.ext; change ∀ i j, raw35967step1 i j = -(raw35967step0 i j); unfold raw35967step1 raw35967step0; decide +kernel
      have hl : raw35967step1Labels = raw35967step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35967step1 raw35967step1Labels = mixedMoment B raw35967step2 raw35967step2Labels := by
      have ha : raw35967step2 = raw35967step1 := by apply Matrix.ext; unfold raw35967step2 raw35967step1; decide +kernel
      have hl : raw35967step1Labels = labelEmbedding10 ∘ raw35967step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35967step1 raw35967step1Labels raw35967step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5217 node5217Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
