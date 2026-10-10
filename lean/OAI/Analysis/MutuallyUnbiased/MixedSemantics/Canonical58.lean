import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7424step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7424 raw7424Labels = mixedMoment B node4400 node4400Labels := by
  calc
    mixedMoment B raw7424 raw7424Labels = mixedMoment B raw7424step0 raw7424step0Labels := by
      have ha : raw7424step0 = (fun i j => raw7424 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7424step0 raw7424; decide +kernel
      have hl : raw7424step0Labels = raw7424Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7424 raw7424Labels permutation154 permutation3
    mixedMoment B raw7424step0 raw7424step0Labels = mixedMoment B raw7424step1 raw7424step1Labels := by
      have ha : raw7424step1 = raw7424step0 := by apply Matrix.ext; unfold raw7424step1 raw7424step0; decide +kernel
      have hl : raw7424step0Labels = labelEmbedding6 ∘ raw7424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7424step0 raw7424step0Labels raw7424step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4400 node4400Labels := by rfl

def raw7425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7425step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7425step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7425 raw7425Labels = mixedMoment B node4999 node4999Labels := by
  calc
    mixedMoment B raw7425 raw7425Labels = mixedMoment B raw7425step0 raw7425step0Labels := by
      have ha : raw7425step0 = (fun i j => raw7425 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7425step0 raw7425; decide +kernel
      have hl : raw7425step0Labels = raw7425Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7425 raw7425Labels permutation154 permutation3
    mixedMoment B raw7425step0 raw7425step0Labels = mixedMoment B raw7425step1 raw7425step1Labels := by
      have ha : raw7425step1 = raw7425step0 := by apply Matrix.ext; unfold raw7425step1 raw7425step0; decide +kernel
      have hl : raw7425step0Labels = labelEmbedding6 ∘ raw7425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7425step0 raw7425step0Labels raw7425step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4999 node4999Labels := by rfl

def raw7426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7426step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7426 raw7426Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw7426 raw7426Labels = mixedMoment B raw7426step0 raw7426step0Labels := by
      have ha : raw7426step0 = (fun i j => raw7426 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7426step0 raw7426; decide +kernel
      have hl : raw7426step0Labels = raw7426Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7426 raw7426Labels permutation178 permutation3
    mixedMoment B raw7426step0 raw7426step0Labels = mixedMoment B raw7426step1 raw7426step1Labels := by
      have ha : raw7426step1 = raw7426step0 := by apply Matrix.ext; unfold raw7426step1 raw7426step0; decide +kernel
      have hl : raw7426step0Labels = labelEmbedding6 ∘ raw7426step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7426step0 raw7426step0Labels raw7426step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw7427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw7427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7427step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7427 raw7427Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw7427 raw7427Labels = mixedMoment B raw7427step0 raw7427step0Labels := by
      have hz : ∀ j, raw7427 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7427step0 = (fun i j => raw7427 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7427step0 raw7427; decide +kernel
      have hl : raw7427step0Labels = raw7427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7427 raw7427Labels permutation520 hz
    mixedMoment B raw7427step0 raw7427step0Labels = mixedMoment B raw7427step1 raw7427step1Labels := by
      have ha : raw7427step1 = (fun i j => raw7427step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7427step1 raw7427step0; decide +kernel
      have hl : raw7427step1Labels = raw7427step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7427step0 raw7427step0Labels permutation32 permutation3
    mixedMoment B raw7427step1 raw7427step1Labels = mixedMoment B raw7427step2 raw7427step2Labels := by
      have ha : raw7427step2 = raw7427step1 := by apply Matrix.ext; unfold raw7427step2 raw7427step1; decide +kernel
      have hl : raw7427step1Labels = labelEmbedding6 ∘ raw7427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7427step1 raw7427step1Labels raw7427step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw7428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7428step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7428 raw7428Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw7428 raw7428Labels = mixedMoment B raw7428step0 raw7428step0Labels := by
      have ha : raw7428step0 = (fun i j => raw7428 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7428step0 raw7428; decide +kernel
      have hl : raw7428step0Labels = raw7428Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7428 raw7428Labels permutation157 permutation3
    mixedMoment B raw7428step0 raw7428step0Labels = mixedMoment B raw7428step1 raw7428step1Labels := by
      have ha : raw7428step1 = raw7428step0 := by apply Matrix.ext; unfold raw7428step1 raw7428step0; decide +kernel
      have hl : raw7428step0Labels = labelEmbedding6 ∘ raw7428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7428step0 raw7428step0Labels raw7428step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw7429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7429step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7429 raw7429Labels = mixedMoment B node4392 node4392Labels := by
  calc
    mixedMoment B raw7429 raw7429Labels = mixedMoment B raw7429step0 raw7429step0Labels := by
      have ha : raw7429step0 = (fun i j => raw7429 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7429step0 raw7429; decide +kernel
      have hl : raw7429step0Labels = raw7429Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7429 raw7429Labels permutation153 permutation3
    mixedMoment B raw7429step0 raw7429step0Labels = mixedMoment B raw7429step1 raw7429step1Labels := by
      have ha : raw7429step1 = raw7429step0 := by apply Matrix.ext; unfold raw7429step1 raw7429step0; decide +kernel
      have hl : raw7429step0Labels = labelEmbedding6 ∘ raw7429step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7429step0 raw7429step0Labels raw7429step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4392 node4392Labels := by rfl

def raw7430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7430step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7430 raw7430Labels = mixedMoment B node4993 node4993Labels := by
  calc
    mixedMoment B raw7430 raw7430Labels = mixedMoment B raw7430step0 raw7430step0Labels := by
      have ha : raw7430step0 = (fun i j => raw7430 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7430step0 raw7430; decide +kernel
      have hl : raw7430step0Labels = raw7430Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7430 raw7430Labels permutation153 permutation3
    mixedMoment B raw7430step0 raw7430step0Labels = mixedMoment B raw7430step1 raw7430step1Labels := by
      have ha : raw7430step1 = raw7430step0 := by apply Matrix.ext; unfold raw7430step1 raw7430step0; decide +kernel
      have hl : raw7430step0Labels = labelEmbedding6 ∘ raw7430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7430step0 raw7430step0Labels raw7430step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4993 node4993Labels := by rfl

def raw7431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7431step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7431 raw7431Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw7431 raw7431Labels = mixedMoment B raw7431step0 raw7431step0Labels := by
      have ha : raw7431step0 = (fun i j => raw7431 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7431step0 raw7431; decide +kernel
      have hl : raw7431step0Labels = raw7431Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7431 raw7431Labels permutation177 permutation3
    mixedMoment B raw7431step0 raw7431step0Labels = mixedMoment B raw7431step1 raw7431step1Labels := by
      have ha : raw7431step1 = raw7431step0 := by apply Matrix.ext; unfold raw7431step1 raw7431step0; decide +kernel
      have hl : raw7431step0Labels = labelEmbedding6 ∘ raw7431step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7431step0 raw7431step0Labels raw7431step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw7432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7432step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7432 raw7432Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw7432 raw7432Labels = mixedMoment B raw7432step0 raw7432step0Labels := by
      have ha : raw7432step0 = (fun i j => raw7432 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7432step0 raw7432; decide +kernel
      have hl : raw7432step0Labels = raw7432Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7432 raw7432Labels permutation201 permutation3
    mixedMoment B raw7432step0 raw7432step0Labels = mixedMoment B raw7432step1 raw7432step1Labels := by
      have ha : raw7432step1 = raw7432step0 := by apply Matrix.ext; unfold raw7432step1 raw7432step0; decide +kernel
      have hl : raw7432step0Labels = labelEmbedding6 ∘ raw7432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7432step0 raw7432step0Labels raw7432step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw7433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw7433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7433step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7433 raw7433Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw7433 raw7433Labels = mixedMoment B raw7433step0 raw7433step0Labels := by
      have ha : raw7433step0 = (fun i j => raw7433 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7433step0 raw7433; decide +kernel
      have hl : raw7433step0Labels = raw7433Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7433 raw7433Labels permutation153 permutation3
    mixedMoment B raw7433step0 raw7433step0Labels = mixedMoment B raw7433step1 raw7433step1Labels := by
      have ha : raw7433step1 = raw7433step0 := by apply Matrix.ext; unfold raw7433step1 raw7433step0; decide +kernel
      have hl : raw7433step0Labels = labelEmbedding6 ∘ raw7433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7433step0 raw7433step0Labels raw7433step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw7434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7434step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7434 raw7434Labels = mixedMoment B node4391 node4391Labels := by
  calc
    mixedMoment B raw7434 raw7434Labels = mixedMoment B raw7434step0 raw7434step0Labels := by
      have ha : raw7434step0 = (fun i j => raw7434 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7434step0 raw7434; decide +kernel
      have hl : raw7434step0Labels = raw7434Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7434 raw7434Labels permutation152 permutation3
    mixedMoment B raw7434step0 raw7434step0Labels = mixedMoment B raw7434step1 raw7434step1Labels := by
      have ha : raw7434step1 = raw7434step0 := by apply Matrix.ext; unfold raw7434step1 raw7434step0; decide +kernel
      have hl : raw7434step0Labels = labelEmbedding6 ∘ raw7434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7434step0 raw7434step0Labels raw7434step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4391 node4391Labels := by rfl

def raw7435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7435step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7435 raw7435Labels = mixedMoment B node4992 node4992Labels := by
  calc
    mixedMoment B raw7435 raw7435Labels = mixedMoment B raw7435step0 raw7435step0Labels := by
      have ha : raw7435step0 = (fun i j => raw7435 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7435step0 raw7435; decide +kernel
      have hl : raw7435step0Labels = raw7435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7435 raw7435Labels permutation152 permutation3
    mixedMoment B raw7435step0 raw7435step0Labels = mixedMoment B raw7435step1 raw7435step1Labels := by
      have ha : raw7435step1 = raw7435step0 := by apply Matrix.ext; unfold raw7435step1 raw7435step0; decide +kernel
      have hl : raw7435step0Labels = labelEmbedding6 ∘ raw7435step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7435step0 raw7435step0Labels raw7435step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4992 node4992Labels := by rfl

def raw7436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7436 raw7436Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw7436 raw7436Labels = mixedMoment B raw7436step0 raw7436step0Labels := by
      have ha : raw7436step0 = (fun i j => raw7436 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7436step0 raw7436; decide +kernel
      have hl : raw7436step0Labels = raw7436Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7436 raw7436Labels permutation676 permutation2
    mixedMoment B raw7436step0 raw7436step0Labels = mixedMoment B raw7436step1 raw7436step1Labels := by
      have ha : raw7436step1 = -raw7436step0 := by apply Matrix.ext; change ∀ i j, raw7436step1 i j = -(raw7436step0 i j); unfold raw7436step1 raw7436step0; decide +kernel
      have hl : raw7436step1Labels = raw7436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw7437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7437 raw7437Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw7437 raw7437Labels = mixedMoment B raw7437step0 raw7437step0Labels := by
      have ha : raw7437step0 = (fun i j => raw7437 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7437step0 raw7437; decide +kernel
      have hl : raw7437step0Labels = raw7437Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7437 raw7437Labels permutation674 permutation2
    mixedMoment B raw7437step0 raw7437step0Labels = mixedMoment B raw7437step1 raw7437step1Labels := by
      have ha : raw7437step1 = -raw7437step0 := by apply Matrix.ext; change ∀ i j, raw7437step1 i j = -(raw7437step0 i j); unfold raw7437step1 raw7437step0; decide +kernel
      have hl : raw7437step1Labels = raw7437step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw7438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw7438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw7438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw7438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw7438step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7438 raw7438Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw7438 raw7438Labels = mixedMoment B raw7438step0 raw7438step0Labels := by
      have hz : ∀ j, raw7438 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7438step0 = (fun i j => raw7438 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7438step0 raw7438; decide +kernel
      have hl : raw7438step0Labels = raw7438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7438 raw7438Labels permutation520 hz
    mixedMoment B raw7438step0 raw7438step0Labels = mixedMoment B raw7438step1 raw7438step1Labels := by
      have ha : raw7438step1 = (fun i j => raw7438step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7438step1 raw7438step0; decide +kernel
      have hl : raw7438step1Labels = raw7438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7438step0 raw7438step0Labels permutation137 permutation2
    mixedMoment B raw7438step1 raw7438step1Labels = mixedMoment B raw7438step2 raw7438step2Labels := by
      have ha : raw7438step2 = -raw7438step1 := by apply Matrix.ext; change ∀ i j, raw7438step2 i j = -(raw7438step1 i j); unfold raw7438step2 raw7438step1; decide +kernel
      have hl : raw7438step2Labels = raw7438step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw7439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7439 raw7439Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw7439 raw7439Labels = mixedMoment B raw7439step0 raw7439step0Labels := by
      have ha : raw7439step0 = (fun i j => raw7439 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7439step0 raw7439; decide +kernel
      have hl : raw7439step0Labels = raw7439Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7439 raw7439Labels permutation152 permutation3
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw7440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7440 raw7440Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw7440 raw7440Labels = mixedMoment B raw7440step0 raw7440step0Labels := by
      have ha : raw7440step0 = (fun i j => raw7440 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7440step0 raw7440; decide +kernel
      have hl : raw7440step0Labels = raw7440Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7440 raw7440Labels permutation176 permutation3
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw7441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7441 raw7441Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw7441 raw7441Labels = mixedMoment B raw7441step0 raw7441step0Labels := by
      have ha : raw7441step0 = (fun i j => raw7441 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7441step0 raw7441; decide +kernel
      have hl : raw7441step0Labels = raw7441Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7441 raw7441Labels permutation200 permutation3
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw7442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7442 raw7442Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw7442 raw7442Labels = mixedMoment B raw7442step0 raw7442step0Labels := by
      have hz : ∀ j, raw7442 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7442step0 = (fun i j => raw7442 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7442step0 raw7442; decide +kernel
      have hl : raw7442step0Labels = raw7442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7442 raw7442Labels permutation520 hz
    mixedMoment B raw7442step0 raw7442step0Labels = mixedMoment B raw7442step1 raw7442step1Labels := by
      have ha : raw7442step1 = (fun i j => raw7442step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7442step1 raw7442step0; decide +kernel
      have hl : raw7442step1Labels = raw7442step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7442step0 raw7442step0Labels permutation32 permutation3
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw7443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7443 raw7443Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw7443 raw7443Labels = mixedMoment B raw7443step0 raw7443step0Labels := by
      have ha : raw7443step0 = (fun i j => raw7443 (permutation617 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7443step0 raw7443; decide +kernel
      have hl : raw7443step0Labels = raw7443Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7443 raw7443Labels permutation617 permutation6
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw7444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7444 raw7444Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw7444 raw7444Labels = mixedMoment B raw7444step0 raw7444step0Labels := by
      have ha : raw7444step0 = (fun i j => raw7444 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7444step0 raw7444; decide +kernel
      have hl : raw7444step0Labels = raw7444Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7444 raw7444Labels permutation182 permutation3
    _ = mixedMoment B node1021 node1021Labels := by rfl

def raw7445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7445 raw7445Labels = mixedMoment B node2570 node2570Labels := by
  calc
    mixedMoment B raw7445 raw7445Labels = mixedMoment B raw7445step0 raw7445step0Labels := by
      have ha : raw7445step0 = (fun i j => raw7445 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7445step0 raw7445; decide +kernel
      have hl : raw7445step0Labels = raw7445Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7445 raw7445Labels permutation182 permutation3
    _ = mixedMoment B node2570 node2570Labels := by rfl

def raw7446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7446 raw7446Labels = mixedMoment B node2570 node2570Labels := by
  calc
    mixedMoment B raw7446 raw7446Labels = mixedMoment B raw7446step0 raw7446step0Labels := by
      have ha : raw7446step0 = (fun i j => raw7446 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7446step0 raw7446; decide +kernel
      have hl : raw7446step0Labels = raw7446Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7446 raw7446Labels permutation206 permutation3
    _ = mixedMoment B node2570 node2570Labels := by rfl

def raw7447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7447step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7447 raw7447Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw7447 raw7447Labels = mixedMoment B raw7447step0 raw7447step0Labels := by
      have hz : ∀ j, raw7447 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7447step0 = (fun i j => raw7447 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7447step0 raw7447; decide +kernel
      have hl : raw7447step0Labels = raw7447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7447 raw7447Labels permutation520 hz
    mixedMoment B raw7447step0 raw7447step0Labels = mixedMoment B raw7447step1 raw7447step1Labels := by
      have ha : raw7447step1 = (fun i j => raw7447step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7447step1 raw7447step0; decide +kernel
      have hl : raw7447step1Labels = raw7447step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7447step0 raw7447step0Labels permutation40 permutation3
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw7448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7448 raw7448Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw7448 raw7448Labels = mixedMoment B raw7448step0 raw7448step0Labels := by
      have ha : raw7448step0 = (fun i j => raw7448 (permutation186 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7448step0 raw7448; decide +kernel
      have hl : raw7448step0Labels = raw7448Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7448 raw7448Labels permutation186 permutation3
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw7449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7449 raw7449Labels = mixedMoment B node981 node981Labels := by
  calc
    mixedMoment B raw7449 raw7449Labels = mixedMoment B raw7449step0 raw7449step0Labels := by
      have ha : raw7449step0 = (fun i j => raw7449 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7449step0 raw7449; decide +kernel
      have hl : raw7449step0Labels = raw7449Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7449 raw7449Labels permutation160 permutation3
    _ = mixedMoment B node981 node981Labels := by rfl

def raw7450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7450 raw7450Labels = mixedMoment B node2384 node2384Labels := by
  calc
    mixedMoment B raw7450 raw7450Labels = mixedMoment B raw7450step0 raw7450step0Labels := by
      have ha : raw7450step0 = (fun i j => raw7450 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7450step0 raw7450; decide +kernel
      have hl : raw7450step0Labels = raw7450Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7450 raw7450Labels permutation160 permutation3
    _ = mixedMoment B node2384 node2384Labels := by rfl

def raw7451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7451 raw7451Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw7451 raw7451Labels = mixedMoment B raw7451step0 raw7451step0Labels := by
      have ha : raw7451step0 = (fun i j => raw7451 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7451step0 raw7451; decide +kernel
      have hl : raw7451step0Labels = raw7451Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7451 raw7451Labels permutation202 permutation3
    _ = mixedMoment B node2557 node2557Labels := by rfl

def raw7452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7452step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7452 raw7452Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw7452 raw7452Labels = mixedMoment B raw7452step0 raw7452step0Labels := by
      have hz : ∀ j, raw7452 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7452step0 = (fun i j => raw7452 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7452step0 raw7452; decide +kernel
      have hl : raw7452step0Labels = raw7452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7452 raw7452Labels permutation520 hz
    mixedMoment B raw7452step0 raw7452step0Labels = mixedMoment B raw7452step1 raw7452step1Labels := by
      have ha : raw7452step1 = (fun i j => raw7452step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7452step1 raw7452step0; decide +kernel
      have hl : raw7452step1Labels = raw7452step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7452step0 raw7452step0Labels permutation34 permutation3
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw7453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7453 raw7453Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw7453 raw7453Labels = mixedMoment B raw7453step0 raw7453step0Labels := by
      have ha : raw7453step0 = (fun i j => raw7453 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7453step0 raw7453; decide +kernel
      have hl : raw7453step0Labels = raw7453Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7453 raw7453Labels permutation163 permutation3
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw7454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7454 raw7454Labels = mixedMoment B node981 node981Labels := by
  calc
    mixedMoment B raw7454 raw7454Labels = mixedMoment B raw7454step0 raw7454step0Labels := by
      have ha : raw7454step0 = (fun i j => raw7454 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7454step0 raw7454; decide +kernel
      have hl : raw7454step0Labels = raw7454Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7454 raw7454Labels permutation154 permutation3
    _ = mixedMoment B node981 node981Labels := by rfl

def raw7455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7455 raw7455Labels = mixedMoment B node2384 node2384Labels := by
  calc
    mixedMoment B raw7455 raw7455Labels = mixedMoment B raw7455step0 raw7455step0Labels := by
      have ha : raw7455step0 = (fun i j => raw7455 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7455step0 raw7455; decide +kernel
      have hl : raw7455step0Labels = raw7455Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7455 raw7455Labels permutation154 permutation3
    _ = mixedMoment B node2384 node2384Labels := by rfl

def raw7456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7456 raw7456Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw7456 raw7456Labels = mixedMoment B raw7456step0 raw7456step0Labels := by
      have ha : raw7456step0 = (fun i j => raw7456 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7456step0 raw7456; decide +kernel
      have hl : raw7456step0Labels = raw7456Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7456 raw7456Labels permutation178 permutation3
    _ = mixedMoment B node2557 node2557Labels := by rfl

def raw7457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw7457step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7457 raw7457Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw7457 raw7457Labels = mixedMoment B raw7457step0 raw7457step0Labels := by
      have hz : ∀ j, raw7457 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7457step0 = (fun i j => raw7457 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7457step0 raw7457; decide +kernel
      have hl : raw7457step0Labels = raw7457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7457 raw7457Labels permutation520 hz
    mixedMoment B raw7457step0 raw7457step0Labels = mixedMoment B raw7457step1 raw7457step1Labels := by
      have ha : raw7457step1 = (fun i j => raw7457step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7457step1 raw7457step0; decide +kernel
      have hl : raw7457step1Labels = raw7457step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7457step0 raw7457step0Labels permutation32 permutation3
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw7458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7458 raw7458Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw7458 raw7458Labels = mixedMoment B raw7458step0 raw7458step0Labels := by
      have ha : raw7458step0 = (fun i j => raw7458 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7458step0 raw7458; decide +kernel
      have hl : raw7458step0Labels = raw7458Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7458 raw7458Labels permutation157 permutation3
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw7459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7459 raw7459Labels = mixedMoment B node973 node973Labels := by
  calc
    mixedMoment B raw7459 raw7459Labels = mixedMoment B raw7459step0 raw7459step0Labels := by
      have ha : raw7459step0 = (fun i j => raw7459 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7459step0 raw7459; decide +kernel
      have hl : raw7459step0Labels = raw7459Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7459 raw7459Labels permutation153 permutation3
    _ = mixedMoment B node973 node973Labels := by rfl

def raw7460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7460 raw7460Labels = mixedMoment B node2379 node2379Labels := by
  calc
    mixedMoment B raw7460 raw7460Labels = mixedMoment B raw7460step0 raw7460step0Labels := by
      have ha : raw7460step0 = (fun i j => raw7460 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7460step0 raw7460; decide +kernel
      have hl : raw7460step0Labels = raw7460Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7460 raw7460Labels permutation153 permutation3
    _ = mixedMoment B node2379 node2379Labels := by rfl

def raw7461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7461 raw7461Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw7461 raw7461Labels = mixedMoment B raw7461step0 raw7461step0Labels := by
      have ha : raw7461step0 = (fun i j => raw7461 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7461step0 raw7461; decide +kernel
      have hl : raw7461step0Labels = raw7461Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7461 raw7461Labels permutation177 permutation3
    _ = mixedMoment B node2545 node2545Labels := by rfl

def raw7462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7462 raw7462Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw7462 raw7462Labels = mixedMoment B raw7462step0 raw7462step0Labels := by
      have ha : raw7462step0 = (fun i j => raw7462 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7462step0 raw7462; decide +kernel
      have hl : raw7462step0Labels = raw7462Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7462 raw7462Labels permutation201 permutation3
    _ = mixedMoment B node2545 node2545Labels := by rfl

def raw7463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw7463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7463 raw7463Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw7463 raw7463Labels = mixedMoment B raw7463step0 raw7463step0Labels := by
      have ha : raw7463step0 = (fun i j => raw7463 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7463step0 raw7463; decide +kernel
      have hl : raw7463step0Labels = raw7463Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7463 raw7463Labels permutation153 permutation3
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw7464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7464 raw7464Labels = mixedMoment B node972 node972Labels := by
  calc
    mixedMoment B raw7464 raw7464Labels = mixedMoment B raw7464step0 raw7464step0Labels := by
      have ha : raw7464step0 = (fun i j => raw7464 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7464step0 raw7464; decide +kernel
      have hl : raw7464step0Labels = raw7464Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7464 raw7464Labels permutation152 permutation3
    _ = mixedMoment B node972 node972Labels := by rfl

def raw7465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7465 raw7465Labels = mixedMoment B node2378 node2378Labels := by
  calc
    mixedMoment B raw7465 raw7465Labels = mixedMoment B raw7465step0 raw7465step0Labels := by
      have ha : raw7465step0 = (fun i j => raw7465 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7465step0 raw7465; decide +kernel
      have hl : raw7465step0Labels = raw7465Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7465 raw7465Labels permutation152 permutation3
    _ = mixedMoment B node2378 node2378Labels := by rfl

def raw7466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7466 raw7466Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw7466 raw7466Labels = mixedMoment B raw7466step0 raw7466step0Labels := by
      have ha : raw7466step0 = (fun i j => raw7466 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7466step0 raw7466; decide +kernel
      have hl : raw7466step0Labels = raw7466Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7466 raw7466Labels permutation176 permutation3
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw7467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7467 raw7467Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw7467 raw7467Labels = mixedMoment B raw7467step0 raw7467step0Labels := by
      have ha : raw7467step0 = (fun i j => raw7467 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7467step0 raw7467; decide +kernel
      have hl : raw7467step0Labels = raw7467Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7467 raw7467Labels permutation200 permutation3
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw7468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw7468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw7468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw7468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7468 raw7468Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw7468 raw7468Labels = mixedMoment B raw7468step0 raw7468step0Labels := by
      have hz : ∀ j, raw7468 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7468step0 = (fun i j => raw7468 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7468step0 raw7468; decide +kernel
      have hl : raw7468step0Labels = raw7468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7468 raw7468Labels permutation520 hz
    mixedMoment B raw7468step0 raw7468step0Labels = mixedMoment B raw7468step1 raw7468step1Labels := by
      have ha : raw7468step1 = (fun i j => raw7468step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7468step1 raw7468step0; decide +kernel
      have hl : raw7468step1Labels = raw7468step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7468step0 raw7468step0Labels permutation32 permutation3
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw7469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7469Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7469step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7469 raw7469Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw7469 raw7469Labels = mixedMoment B raw7469step0 raw7469step0Labels := by
      have ha : raw7469step0 = (fun i j => raw7469 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7469step0 raw7469; decide +kernel
      have hl : raw7469step0Labels = raw7469Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7469 raw7469Labels permutation620 permutation7
    mixedMoment B raw7469step0 raw7469step0Labels = mixedMoment B raw7469step1 raw7469step1Labels := by
      have ha : raw7469step1 = raw7469step0 := by apply Matrix.ext; unfold raw7469step1 raw7469step0; decide +kernel
      have hl : raw7469step0Labels = labelEmbedding1 ∘ raw7469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7469step0 raw7469step0Labels raw7469step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw7470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7470step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7470 raw7470Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw7470 raw7470Labels = mixedMoment B raw7470step0 raw7470step0Labels := by
      have ha : raw7470step0 = (fun i j => raw7470 (permutation622 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7470step0 raw7470; decide +kernel
      have hl : raw7470step0Labels = raw7470Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7470 raw7470Labels permutation622 permutation7
    mixedMoment B raw7470step0 raw7470step0Labels = mixedMoment B raw7470step1 raw7470step1Labels := by
      have ha : raw7470step1 = raw7470step0 := by apply Matrix.ext; unfold raw7470step1 raw7470step0; decide +kernel
      have hl : raw7470step0Labels = labelEmbedding1 ∘ raw7470step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7470step0 raw7470step0Labels raw7470step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw7471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7471Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7471step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7471 raw7471Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw7471 raw7471Labels = mixedMoment B raw7471step0 raw7471step0Labels := by
      have ha : raw7471step0 = (fun i j => raw7471 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7471step0 raw7471; decide +kernel
      have hl : raw7471step0Labels = raw7471Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7471 raw7471Labels permutation620 permutation7
    mixedMoment B raw7471step0 raw7471step0Labels = mixedMoment B raw7471step1 raw7471step1Labels := by
      have ha : raw7471step1 = raw7471step0 := by apply Matrix.ext; unfold raw7471step1 raw7471step0; decide +kernel
      have hl : raw7471step0Labels = labelEmbedding1 ∘ raw7471step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7471step0 raw7471step0Labels raw7471step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw7472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7472Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7472step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7472step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7472 raw7472Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw7472 raw7472Labels = mixedMoment B raw7472step0 raw7472step0Labels := by
      have hz : ∀ j, raw7472 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7472step0 = (fun i j => raw7472 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7472step0 raw7472; decide +kernel
      have hl : raw7472step0Labels = raw7472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7472 raw7472Labels permutation520 hz
    mixedMoment B raw7472step0 raw7472step0Labels = mixedMoment B raw7472step1 raw7472step1Labels := by
      have ha : raw7472step1 = (fun i j => raw7472step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7472step1 raw7472step0; decide +kernel
      have hl : raw7472step1Labels = raw7472step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7472step0 raw7472step0Labels permutation137 permutation7
    mixedMoment B raw7472step1 raw7472step1Labels = mixedMoment B raw7472step2 raw7472step2Labels := by
      have ha : raw7472step2 = raw7472step1 := by apply Matrix.ext; unfold raw7472step2 raw7472step1; decide +kernel
      have hl : raw7472step1Labels = labelEmbedding1 ∘ raw7472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7472step1 raw7472step1Labels raw7472step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw7473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7473Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7473step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7473 raw7473Labels = mixedMoment B node3991 node3991Labels := by
  calc
    mixedMoment B raw7473 raw7473Labels = mixedMoment B raw7473step0 raw7473step0Labels := by
      have ha : raw7473step0 = (fun i j => raw7473 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7473step0 raw7473; decide +kernel
      have hl : raw7473step0Labels = raw7473Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7473 raw7473Labels permutation620 permutation7
    mixedMoment B raw7473step0 raw7473step0Labels = mixedMoment B raw7473step1 raw7473step1Labels := by
      have ha : raw7473step1 = raw7473step0 := by apply Matrix.ext; unfold raw7473step1 raw7473step0; decide +kernel
      have hl : raw7473step0Labels = labelEmbedding1 ∘ raw7473step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7473step0 raw7473step0Labels raw7473step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3991 node3991Labels := by rfl

def raw7474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7474Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7474step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7474step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7474 raw7474Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw7474 raw7474Labels = mixedMoment B raw7474step0 raw7474step0Labels := by
      have ha : raw7474step0 = (fun i j => raw7474 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7474step0 raw7474; decide +kernel
      have hl : raw7474step0Labels = raw7474Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7474 raw7474Labels permutation170 permutation5
    mixedMoment B raw7474step0 raw7474step0Labels = mixedMoment B raw7474step1 raw7474step1Labels := by
      have ha : raw7474step1 = -raw7474step0 := by apply Matrix.ext; change ∀ i j, raw7474step1 i j = -(raw7474step0 i j); unfold raw7474step1 raw7474step0; decide +kernel
      have hl : raw7474step1Labels = raw7474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7474step1 raw7474step1Labels = mixedMoment B raw7474step2 raw7474step2Labels := by
      have ha : raw7474step2 = raw7474step1 := by apply Matrix.ext; unfold raw7474step2 raw7474step1; decide +kernel
      have hl : raw7474step1Labels = labelEmbedding1 ∘ raw7474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7474step1 raw7474step1Labels raw7474step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw7475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7475Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw7475step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7475step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7475step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7475 raw7475Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw7475 raw7475Labels = mixedMoment B raw7475step0 raw7475step0Labels := by
      have ha : raw7475step0 = (fun i j => raw7475 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7475step0 raw7475; decide +kernel
      have hl : raw7475step0Labels = raw7475Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7475 raw7475Labels permutation180 permutation5
    mixedMoment B raw7475step0 raw7475step0Labels = mixedMoment B raw7475step1 raw7475step1Labels := by
      have ha : raw7475step1 = -raw7475step0 := by apply Matrix.ext; change ∀ i j, raw7475step1 i j = -(raw7475step0 i j); unfold raw7475step1 raw7475step0; decide +kernel
      have hl : raw7475step1Labels = raw7475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7475step1 raw7475step1Labels = mixedMoment B raw7475step2 raw7475step2Labels := by
      have ha : raw7475step2 = raw7475step1 := by apply Matrix.ext; unfold raw7475step2 raw7475step1; decide +kernel
      have hl : raw7475step1Labels = labelEmbedding1 ∘ raw7475step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7475step1 raw7475step1Labels raw7475step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw7476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7476Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw7476step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7476step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7476step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7476 raw7476Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw7476 raw7476Labels = mixedMoment B raw7476step0 raw7476step0Labels := by
      have ha : raw7476step0 = (fun i j => raw7476 (permutation204 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7476step0 raw7476; decide +kernel
      have hl : raw7476step0Labels = raw7476Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7476 raw7476Labels permutation204 permutation5
    mixedMoment B raw7476step0 raw7476step0Labels = mixedMoment B raw7476step1 raw7476step1Labels := by
      have ha : raw7476step1 = -raw7476step0 := by apply Matrix.ext; change ∀ i j, raw7476step1 i j = -(raw7476step0 i j); unfold raw7476step1 raw7476step0; decide +kernel
      have hl : raw7476step1Labels = raw7476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7476step1 raw7476step1Labels = mixedMoment B raw7476step2 raw7476step2Labels := by
      have ha : raw7476step2 = raw7476step1 := by apply Matrix.ext; unfold raw7476step2 raw7476step1; decide +kernel
      have hl : raw7476step1Labels = labelEmbedding1 ∘ raw7476step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7476step1 raw7476step1Labels raw7476step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw7477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7477Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7477step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw7477step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw7477step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7477step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw7477step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7477 raw7477Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw7477 raw7477Labels = mixedMoment B raw7477step0 raw7477step0Labels := by
      have hz : ∀ j, raw7477 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7477step0 = (fun i j => raw7477 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7477step0 raw7477; decide +kernel
      have hl : raw7477step0Labels = raw7477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7477 raw7477Labels permutation520 hz
    mixedMoment B raw7477step0 raw7477step0Labels = mixedMoment B raw7477step1 raw7477step1Labels := by
      have ha : raw7477step1 = (fun i j => raw7477step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7477step1 raw7477step0; decide +kernel
      have hl : raw7477step1Labels = raw7477step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7477step0 raw7477step0Labels permutation36 permutation5
    mixedMoment B raw7477step1 raw7477step1Labels = mixedMoment B raw7477step2 raw7477step2Labels := by
      have ha : raw7477step2 = -raw7477step1 := by apply Matrix.ext; change ∀ i j, raw7477step2 i j = -(raw7477step1 i j); unfold raw7477step2 raw7477step1; decide +kernel
      have hl : raw7477step2Labels = raw7477step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7477step2 raw7477step2Labels = mixedMoment B raw7477step3 raw7477step3Labels := by
      have ha : raw7477step3 = raw7477step2 := by apply Matrix.ext; unfold raw7477step3 raw7477step2; decide +kernel
      have hl : raw7477step2Labels = labelEmbedding1 ∘ raw7477step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7477step2 raw7477step2Labels raw7477step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw7478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7478Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7478step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7478step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7478 raw7478Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw7478 raw7478Labels = mixedMoment B raw7478step0 raw7478step0Labels := by
      have ha : raw7478step0 = (fun i j => raw7478 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7478step0 raw7478; decide +kernel
      have hl : raw7478step0Labels = raw7478Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7478 raw7478Labels permutation246 permutation5
    mixedMoment B raw7478step0 raw7478step0Labels = mixedMoment B raw7478step1 raw7478step1Labels := by
      have ha : raw7478step1 = -raw7478step0 := by apply Matrix.ext; change ∀ i j, raw7478step1 i j = -(raw7478step0 i j); unfold raw7478step1 raw7478step0; decide +kernel
      have hl : raw7478step1Labels = raw7478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7478step1 raw7478step1Labels = mixedMoment B raw7478step2 raw7478step2Labels := by
      have ha : raw7478step2 = raw7478step1 := by apply Matrix.ext; unfold raw7478step2 raw7478step1; decide +kernel
      have hl : raw7478step1Labels = labelEmbedding1 ∘ raw7478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7478step1 raw7478step1Labels raw7478step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw7479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7479Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7479step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7479step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7479step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7479step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7479 raw7479Labels = mixedMoment B node1607 node1607Labels := by
  calc
    mixedMoment B raw7479 raw7479Labels = mixedMoment B raw7479step0 raw7479step0Labels := by
      have ha : raw7479step0 = (fun i j => raw7479 (permutation173 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7479step0 raw7479; decide +kernel
      have hl : raw7479step0Labels = raw7479Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7479 raw7479Labels permutation173 permutation5
    mixedMoment B raw7479step0 raw7479step0Labels = mixedMoment B raw7479step1 raw7479step1Labels := by
      have ha : raw7479step1 = -raw7479step0 := by apply Matrix.ext; change ∀ i j, raw7479step1 i j = -(raw7479step0 i j); unfold raw7479step1 raw7479step0; decide +kernel
      have hl : raw7479step1Labels = raw7479step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7479step1 raw7479step1Labels = mixedMoment B raw7479step2 raw7479step2Labels := by
      have ha : raw7479step2 = raw7479step1 := by apply Matrix.ext; unfold raw7479step2 raw7479step1; decide +kernel
      have hl : raw7479step1Labels = labelEmbedding1 ∘ raw7479step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7479step1 raw7479step1Labels raw7479step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1607 node1607Labels := by rfl

def raw7480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7480Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7480step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7480step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7480 raw7480Labels = mixedMoment B node3346 node3346Labels := by
  calc
    mixedMoment B raw7480 raw7480Labels = mixedMoment B raw7480step0 raw7480step0Labels := by
      have ha : raw7480step0 = (fun i j => raw7480 (permutation173 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7480step0 raw7480; decide +kernel
      have hl : raw7480step0Labels = raw7480Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7480 raw7480Labels permutation173 permutation5
    mixedMoment B raw7480step0 raw7480step0Labels = mixedMoment B raw7480step1 raw7480step1Labels := by
      have ha : raw7480step1 = -raw7480step0 := by apply Matrix.ext; change ∀ i j, raw7480step1 i j = -(raw7480step0 i j); unfold raw7480step1 raw7480step0; decide +kernel
      have hl : raw7480step1Labels = raw7480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7480step1 raw7480step1Labels = mixedMoment B raw7480step2 raw7480step2Labels := by
      have ha : raw7480step2 = raw7480step1 := by apply Matrix.ext; unfold raw7480step2 raw7480step1; decide +kernel
      have hl : raw7480step1Labels = labelEmbedding1 ∘ raw7480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7480step1 raw7480step1Labels raw7480step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3346 node3346Labels := by rfl

def raw7481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7481Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw7481step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7481step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7481step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7481 raw7481Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw7481 raw7481Labels = mixedMoment B raw7481step0 raw7481step0Labels := by
      have ha : raw7481step0 = (fun i j => raw7481 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7481step0 raw7481; decide +kernel
      have hl : raw7481step0Labels = raw7481Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7481 raw7481Labels permutation163 permutation5
    mixedMoment B raw7481step0 raw7481step0Labels = mixedMoment B raw7481step1 raw7481step1Labels := by
      have ha : raw7481step1 = -raw7481step0 := by apply Matrix.ext; change ∀ i j, raw7481step1 i j = -(raw7481step0 i j); unfold raw7481step1 raw7481step0; decide +kernel
      have hl : raw7481step1Labels = raw7481step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7481step1 raw7481step1Labels = mixedMoment B raw7481step2 raw7481step2Labels := by
      have ha : raw7481step2 = raw7481step1 := by apply Matrix.ext; unfold raw7481step2 raw7481step1; decide +kernel
      have hl : raw7481step1Labels = labelEmbedding1 ∘ raw7481step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7481step1 raw7481step1Labels raw7481step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw7482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7482Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7482step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw7482step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7482step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7482step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7482step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7482 raw7482Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw7482 raw7482Labels = mixedMoment B raw7482step0 raw7482step0Labels := by
      have hz : ∀ j, raw7482 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7482step0 = (fun i j => raw7482 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7482step0 raw7482; decide +kernel
      have hl : raw7482step0Labels = raw7482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7482 raw7482Labels permutation520 hz
    mixedMoment B raw7482step0 raw7482step0Labels = mixedMoment B raw7482step1 raw7482step1Labels := by
      have ha : raw7482step1 = (fun i j => raw7482step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7482step1 raw7482step0; decide +kernel
      have hl : raw7482step1Labels = raw7482step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7482step0 raw7482step0Labels permutation37 permutation5
    mixedMoment B raw7482step1 raw7482step1Labels = mixedMoment B raw7482step2 raw7482step2Labels := by
      have ha : raw7482step2 = -raw7482step1 := by apply Matrix.ext; change ∀ i j, raw7482step2 i j = -(raw7482step1 i j); unfold raw7482step2 raw7482step1; decide +kernel
      have hl : raw7482step2Labels = raw7482step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7482step2 raw7482step2Labels = mixedMoment B raw7482step3 raw7482step3Labels := by
      have ha : raw7482step3 = raw7482step2 := by apply Matrix.ext; unfold raw7482step3 raw7482step2; decide +kernel
      have hl : raw7482step2Labels = labelEmbedding1 ∘ raw7482step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7482step2 raw7482step2Labels raw7482step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw7483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7483Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7483step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7483step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7483step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7483 raw7483Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw7483 raw7483Labels = mixedMoment B raw7483step0 raw7483step0Labels := by
      have ha : raw7483step0 = (fun i j => raw7483 (permutation173 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7483step0 raw7483; decide +kernel
      have hl : raw7483step0Labels = raw7483Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7483 raw7483Labels permutation173 permutation5
    mixedMoment B raw7483step0 raw7483step0Labels = mixedMoment B raw7483step1 raw7483step1Labels := by
      have ha : raw7483step1 = -raw7483step0 := by apply Matrix.ext; change ∀ i j, raw7483step1 i j = -(raw7483step0 i j); unfold raw7483step1 raw7483step0; decide +kernel
      have hl : raw7483step1Labels = raw7483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7483step1 raw7483step1Labels = mixedMoment B raw7483step2 raw7483step2Labels := by
      have ha : raw7483step2 = raw7483step1 := by apply Matrix.ext; unfold raw7483step2 raw7483step1; decide +kernel
      have hl : raw7483step1Labels = labelEmbedding1 ∘ raw7483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7483step1 raw7483step1Labels raw7483step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3503 node3503Labels := by rfl

def raw7484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7484Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7484step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7484step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7484step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7484 raw7484Labels = mixedMoment B node1607 node1607Labels := by
  calc
    mixedMoment B raw7484 raw7484Labels = mixedMoment B raw7484step0 raw7484step0Labels := by
      have ha : raw7484step0 = (fun i j => raw7484 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7484step0 raw7484; decide +kernel
      have hl : raw7484step0Labels = raw7484Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7484 raw7484Labels permutation171 permutation5
    mixedMoment B raw7484step0 raw7484step0Labels = mixedMoment B raw7484step1 raw7484step1Labels := by
      have ha : raw7484step1 = -raw7484step0 := by apply Matrix.ext; change ∀ i j, raw7484step1 i j = -(raw7484step0 i j); unfold raw7484step1 raw7484step0; decide +kernel
      have hl : raw7484step1Labels = raw7484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7484step1 raw7484step1Labels = mixedMoment B raw7484step2 raw7484step2Labels := by
      have ha : raw7484step2 = raw7484step1 := by apply Matrix.ext; unfold raw7484step2 raw7484step1; decide +kernel
      have hl : raw7484step1Labels = labelEmbedding1 ∘ raw7484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7484step1 raw7484step1Labels raw7484step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1607 node1607Labels := by rfl

def raw7485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7485Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7485step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7485step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7485step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7485 raw7485Labels = mixedMoment B node3346 node3346Labels := by
  calc
    mixedMoment B raw7485 raw7485Labels = mixedMoment B raw7485step0 raw7485step0Labels := by
      have ha : raw7485step0 = (fun i j => raw7485 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7485step0 raw7485; decide +kernel
      have hl : raw7485step0Labels = raw7485Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7485 raw7485Labels permutation171 permutation5
    mixedMoment B raw7485step0 raw7485step0Labels = mixedMoment B raw7485step1 raw7485step1Labels := by
      have ha : raw7485step1 = -raw7485step0 := by apply Matrix.ext; change ∀ i j, raw7485step1 i j = -(raw7485step0 i j); unfold raw7485step1 raw7485step0; decide +kernel
      have hl : raw7485step1Labels = raw7485step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7485step1 raw7485step1Labels = mixedMoment B raw7485step2 raw7485step2Labels := by
      have ha : raw7485step2 = raw7485step1 := by apply Matrix.ext; unfold raw7485step2 raw7485step1; decide +kernel
      have hl : raw7485step1Labels = labelEmbedding1 ∘ raw7485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7485step1 raw7485step1Labels raw7485step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3346 node3346Labels := by rfl

def raw7486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7486Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw7486step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7486step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7486 raw7486Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw7486 raw7486Labels = mixedMoment B raw7486step0 raw7486step0Labels := by
      have ha : raw7486step0 = (fun i j => raw7486 (permutation157 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7486step0 raw7486; decide +kernel
      have hl : raw7486step0Labels = raw7486Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7486 raw7486Labels permutation157 permutation5
    mixedMoment B raw7486step0 raw7486step0Labels = mixedMoment B raw7486step1 raw7486step1Labels := by
      have ha : raw7486step1 = -raw7486step0 := by apply Matrix.ext; change ∀ i j, raw7486step1 i j = -(raw7486step0 i j); unfold raw7486step1 raw7486step0; decide +kernel
      have hl : raw7486step1Labels = raw7486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7486step1 raw7486step1Labels = mixedMoment B raw7486step2 raw7486step2Labels := by
      have ha : raw7486step2 = raw7486step1 := by apply Matrix.ext; unfold raw7486step2 raw7486step1; decide +kernel
      have hl : raw7486step1Labels = labelEmbedding1 ∘ raw7486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7486step1 raw7486step1Labels raw7486step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw7487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7487Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw7487step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw7487step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7487step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7487step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7487step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7487 raw7487Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw7487 raw7487Labels = mixedMoment B raw7487step0 raw7487step0Labels := by
      have hz : ∀ j, raw7487 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7487step0 = (fun i j => raw7487 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7487step0 raw7487; decide +kernel
      have hl : raw7487step0Labels = raw7487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7487 raw7487Labels permutation520 hz
    mixedMoment B raw7487step0 raw7487step0Labels = mixedMoment B raw7487step1 raw7487step1Labels := by
      have ha : raw7487step1 = (fun i j => raw7487step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7487step1 raw7487step0; decide +kernel
      have hl : raw7487step1Labels = raw7487step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7487step0 raw7487step0Labels permutation36 permutation5
    mixedMoment B raw7487step1 raw7487step1Labels = mixedMoment B raw7487step2 raw7487step2Labels := by
      have ha : raw7487step2 = -raw7487step1 := by apply Matrix.ext; change ∀ i j, raw7487step2 i j = -(raw7487step1 i j); unfold raw7487step2 raw7487step1; decide +kernel
      have hl : raw7487step2Labels = raw7487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7487step2 raw7487step2Labels = mixedMoment B raw7487step3 raw7487step3Labels := by
      have ha : raw7487step3 = raw7487step2 := by apply Matrix.ext; unfold raw7487step3 raw7487step2; decide +kernel
      have hl : raw7487step2Labels = labelEmbedding1 ∘ raw7487step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7487step2 raw7487step2Labels raw7487step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw7488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7488Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7488step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7488step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7488step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7488 raw7488Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw7488 raw7488Labels = mixedMoment B raw7488step0 raw7488step0Labels := by
      have ha : raw7488step0 = (fun i j => raw7488 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7488step0 raw7488; decide +kernel
      have hl : raw7488step0Labels = raw7488Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7488 raw7488Labels permutation171 permutation5
    mixedMoment B raw7488step0 raw7488step0Labels = mixedMoment B raw7488step1 raw7488step1Labels := by
      have ha : raw7488step1 = -raw7488step0 := by apply Matrix.ext; change ∀ i j, raw7488step1 i j = -(raw7488step0 i j); unfold raw7488step1 raw7488step0; decide +kernel
      have hl : raw7488step1Labels = raw7488step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7488step1 raw7488step1Labels = mixedMoment B raw7488step2 raw7488step2Labels := by
      have ha : raw7488step2 = raw7488step1 := by apply Matrix.ext; unfold raw7488step2 raw7488step1; decide +kernel
      have hl : raw7488step1Labels = labelEmbedding1 ∘ raw7488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7488step1 raw7488step1Labels raw7488step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3503 node3503Labels := by rfl

def raw7489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7489Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7489step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7489step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7489 raw7489Labels = mixedMoment B node1606 node1606Labels := by
  calc
    mixedMoment B raw7489 raw7489Labels = mixedMoment B raw7489step0 raw7489step0Labels := by
      have ha : raw7489step0 = (fun i j => raw7489 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7489step0 raw7489; decide +kernel
      have hl : raw7489step0Labels = raw7489Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7489 raw7489Labels permutation170 permutation5
    mixedMoment B raw7489step0 raw7489step0Labels = mixedMoment B raw7489step1 raw7489step1Labels := by
      have ha : raw7489step1 = -raw7489step0 := by apply Matrix.ext; change ∀ i j, raw7489step1 i j = -(raw7489step0 i j); unfold raw7489step1 raw7489step0; decide +kernel
      have hl : raw7489step1Labels = raw7489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7489step1 raw7489step1Labels = mixedMoment B raw7489step2 raw7489step2Labels := by
      have ha : raw7489step2 = raw7489step1 := by apply Matrix.ext; unfold raw7489step2 raw7489step1; decide +kernel
      have hl : raw7489step1Labels = labelEmbedding1 ∘ raw7489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7489step1 raw7489step1Labels raw7489step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1606 node1606Labels := by rfl

def raw7490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7490Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7490 raw7490Labels = mixedMoment B node3345 node3345Labels := by
  calc
    mixedMoment B raw7490 raw7490Labels = mixedMoment B raw7490step0 raw7490step0Labels := by
      have ha : raw7490step0 = (fun i j => raw7490 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7490step0 raw7490; decide +kernel
      have hl : raw7490step0Labels = raw7490Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7490 raw7490Labels permutation170 permutation5
    mixedMoment B raw7490step0 raw7490step0Labels = mixedMoment B raw7490step1 raw7490step1Labels := by
      have ha : raw7490step1 = -raw7490step0 := by apply Matrix.ext; change ∀ i j, raw7490step1 i j = -(raw7490step0 i j); unfold raw7490step1 raw7490step0; decide +kernel
      have hl : raw7490step1Labels = raw7490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7490step1 raw7490step1Labels = mixedMoment B raw7490step2 raw7490step2Labels := by
      have ha : raw7490step2 = raw7490step1 := by apply Matrix.ext; unfold raw7490step2 raw7490step1; decide +kernel
      have hl : raw7490step1Labels = labelEmbedding1 ∘ raw7490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7490step1 raw7490step1Labels raw7490step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3345 node3345Labels := by rfl

def raw7491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw7491step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7491step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7491step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7491step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7491 raw7491Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw7491 raw7491Labels = mixedMoment B raw7491step0 raw7491step0Labels := by
      have ha : raw7491step0 = (fun i j => raw7491 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7491step0 raw7491; decide +kernel
      have hl : raw7491step0Labels = raw7491Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7491 raw7491Labels permutation156 permutation5
    mixedMoment B raw7491step0 raw7491step0Labels = mixedMoment B raw7491step1 raw7491step1Labels := by
      have ha : raw7491step1 = -raw7491step0 := by apply Matrix.ext; change ∀ i j, raw7491step1 i j = -(raw7491step0 i j); unfold raw7491step1 raw7491step0; decide +kernel
      have hl : raw7491step1Labels = raw7491step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7491step1 raw7491step1Labels = mixedMoment B raw7491step2 raw7491step2Labels := by
      have ha : raw7491step2 = raw7491step1 := by apply Matrix.ext; unfold raw7491step2 raw7491step1; decide +kernel
      have hl : raw7491step1Labels = labelEmbedding1 ∘ raw7491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7491step1 raw7491step1Labels raw7491step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw7492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw7492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7492step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7492step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7492 raw7492Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw7492 raw7492Labels = mixedMoment B raw7492step0 raw7492step0Labels := by
      have ha : raw7492step0 = (fun i j => raw7492 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7492step0 raw7492; decide +kernel
      have hl : raw7492step0Labels = raw7492Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7492 raw7492Labels permutation162 permutation5
    mixedMoment B raw7492step0 raw7492step0Labels = mixedMoment B raw7492step1 raw7492step1Labels := by
      have ha : raw7492step1 = -raw7492step0 := by apply Matrix.ext; change ∀ i j, raw7492step1 i j = -(raw7492step0 i j); unfold raw7492step1 raw7492step0; decide +kernel
      have hl : raw7492step1Labels = raw7492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7492step1 raw7492step1Labels = mixedMoment B raw7492step2 raw7492step2Labels := by
      have ha : raw7492step2 = raw7492step1 := by apply Matrix.ext; unfold raw7492step2 raw7492step1; decide +kernel
      have hl : raw7492step1Labels = labelEmbedding1 ∘ raw7492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7492step1 raw7492step1Labels raw7492step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw7493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw7493Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7493step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7493step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7493step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7493 raw7493Labels = mixedMoment B node3502 node3502Labels := by
  calc
    mixedMoment B raw7493 raw7493Labels = mixedMoment B raw7493step0 raw7493step0Labels := by
      have ha : raw7493step0 = (fun i j => raw7493 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7493step0 raw7493; decide +kernel
      have hl : raw7493step0Labels = raw7493Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7493 raw7493Labels permutation170 permutation5
    mixedMoment B raw7493step0 raw7493step0Labels = mixedMoment B raw7493step1 raw7493step1Labels := by
      have ha : raw7493step1 = -raw7493step0 := by apply Matrix.ext; change ∀ i j, raw7493step1 i j = -(raw7493step0 i j); unfold raw7493step1 raw7493step0; decide +kernel
      have hl : raw7493step1Labels = raw7493step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7493step1 raw7493step1Labels = mixedMoment B raw7493step2 raw7493step2Labels := by
      have ha : raw7493step2 = raw7493step1 := by apply Matrix.ext; unfold raw7493step2 raw7493step1; decide +kernel
      have hl : raw7493step1Labels = labelEmbedding1 ∘ raw7493step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7493step1 raw7493step1Labels raw7493step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3502 node3502Labels := by rfl

def raw7494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw7494step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7494step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7494step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7494 raw7494Labels = mixedMoment B node1613 node1613Labels := by
  calc
    mixedMoment B raw7494 raw7494Labels = mixedMoment B raw7494step0 raw7494step0Labels := by
      have ha : raw7494step0 = (fun i j => raw7494 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7494step0 raw7494; decide +kernel
      have hl : raw7494step0Labels = raw7494Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7494 raw7494Labels permutation152 permutation5
    mixedMoment B raw7494step0 raw7494step0Labels = mixedMoment B raw7494step1 raw7494step1Labels := by
      have ha : raw7494step1 = -raw7494step0 := by apply Matrix.ext; change ∀ i j, raw7494step1 i j = -(raw7494step0 i j); unfold raw7494step1 raw7494step0; decide +kernel
      have hl : raw7494step1Labels = raw7494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7494step1 raw7494step1Labels = mixedMoment B raw7494step2 raw7494step2Labels := by
      have ha : raw7494step2 = raw7494step1 := by apply Matrix.ext; unfold raw7494step2 raw7494step1; decide +kernel
      have hl : raw7494step1Labels = labelEmbedding1 ∘ raw7494step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7494step1 raw7494step1Labels raw7494step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1613 node1613Labels := by rfl

def raw7495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw7495step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7495step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7495 raw7495Labels = mixedMoment B node3350 node3350Labels := by
  calc
    mixedMoment B raw7495 raw7495Labels = mixedMoment B raw7495step0 raw7495step0Labels := by
      have ha : raw7495step0 = (fun i j => raw7495 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7495step0 raw7495; decide +kernel
      have hl : raw7495step0Labels = raw7495Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7495 raw7495Labels permutation152 permutation5
    mixedMoment B raw7495step0 raw7495step0Labels = mixedMoment B raw7495step1 raw7495step1Labels := by
      have ha : raw7495step1 = -raw7495step0 := by apply Matrix.ext; change ∀ i j, raw7495step1 i j = -(raw7495step0 i j); unfold raw7495step1 raw7495step0; decide +kernel
      have hl : raw7495step1Labels = raw7495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7495step1 raw7495step1Labels = mixedMoment B raw7495step2 raw7495step2Labels := by
      have ha : raw7495step2 = raw7495step1 := by apply Matrix.ext; unfold raw7495step2 raw7495step1; decide +kernel
      have hl : raw7495step1Labels = labelEmbedding1 ∘ raw7495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7495step1 raw7495step1Labels raw7495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3350 node3350Labels := by rfl

def raw7496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw7496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7496step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7496 raw7496Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw7496 raw7496Labels = mixedMoment B raw7496step0 raw7496step0Labels := by
      have ha : raw7496step0 = (fun i j => raw7496 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7496step0 raw7496; decide +kernel
      have hl : raw7496step0Labels = raw7496Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7496 raw7496Labels permutation152 permutation5
    mixedMoment B raw7496step0 raw7496step0Labels = mixedMoment B raw7496step1 raw7496step1Labels := by
      have ha : raw7496step1 = -raw7496step0 := by apply Matrix.ext; change ∀ i j, raw7496step1 i j = -(raw7496step0 i j); unfold raw7496step1 raw7496step0; decide +kernel
      have hl : raw7496step1Labels = raw7496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7496step1 raw7496step1Labels = mixedMoment B raw7496step2 raw7496step2Labels := by
      have ha : raw7496step2 = raw7496step1 := by apply Matrix.ext; unfold raw7496step2 raw7496step1; decide +kernel
      have hl : raw7496step1Labels = labelEmbedding1 ∘ raw7496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7496step1 raw7496step1Labels raw7496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw7497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw7497step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7497step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7497 raw7497Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw7497 raw7497Labels = mixedMoment B raw7497step0 raw7497step0Labels := by
      have ha : raw7497step0 = (fun i j => raw7497 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7497step0 raw7497; decide +kernel
      have hl : raw7497step0Labels = raw7497Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7497 raw7497Labels permutation158 permutation5
    mixedMoment B raw7497step0 raw7497step0Labels = mixedMoment B raw7497step1 raw7497step1Labels := by
      have ha : raw7497step1 = -raw7497step0 := by apply Matrix.ext; change ∀ i j, raw7497step1 i j = -(raw7497step0 i j); unfold raw7497step1 raw7497step0; decide +kernel
      have hl : raw7497step1Labels = raw7497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7497step1 raw7497step1Labels = mixedMoment B raw7497step2 raw7497step2Labels := by
      have ha : raw7497step2 = raw7497step1 := by apply Matrix.ext; unfold raw7497step2 raw7497step1; decide +kernel
      have hl : raw7497step1Labels = labelEmbedding1 ∘ raw7497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7497step1 raw7497step1Labels raw7497step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw7498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw7498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw7498step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw7498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7498step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7498step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7498step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7498 raw7498Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw7498 raw7498Labels = mixedMoment B raw7498step0 raw7498step0Labels := by
      have hz : ∀ j, raw7498 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7498step0 = (fun i j => raw7498 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7498step0 raw7498; decide +kernel
      have hl : raw7498step0Labels = raw7498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7498 raw7498Labels permutation520 hz
    mixedMoment B raw7498step0 raw7498step0Labels = mixedMoment B raw7498step1 raw7498step1Labels := by
      have ha : raw7498step1 = (fun i j => raw7498step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7498step1 raw7498step0; decide +kernel
      have hl : raw7498step1Labels = raw7498step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7498step0 raw7498step0Labels permutation32 permutation5
    mixedMoment B raw7498step1 raw7498step1Labels = mixedMoment B raw7498step2 raw7498step2Labels := by
      have ha : raw7498step2 = -raw7498step1 := by apply Matrix.ext; change ∀ i j, raw7498step2 i j = -(raw7498step1 i j); unfold raw7498step2 raw7498step1; decide +kernel
      have hl : raw7498step2Labels = raw7498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7498step2 raw7498step2Labels = mixedMoment B raw7498step3 raw7498step3Labels := by
      have ha : raw7498step3 = raw7498step2 := by apply Matrix.ext; unfold raw7498step3 raw7498step2; decide +kernel
      have hl : raw7498step2Labels = labelEmbedding1 ∘ raw7498step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7498step2 raw7498step2Labels raw7498step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw7499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7499 raw7499Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw7499 raw7499Labels = mixedMoment B raw7499step0 raw7499step0Labels := by
      have ha : raw7499step0 = (fun i j => raw7499 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7499step0 raw7499; decide +kernel
      have hl : raw7499step0Labels = raw7499Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7499 raw7499Labels permutation182 permutation2
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw7500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw7500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7500 raw7500Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw7500 raw7500Labels = mixedMoment B raw7500step0 raw7500step0Labels := by
      have ha : raw7500step0 = (fun i j => raw7500 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7500step0 raw7500; decide +kernel
      have hl : raw7500step0Labels = raw7500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7500 raw7500Labels permutation682 permutation2
    mixedMoment B raw7500step0 raw7500step0Labels = mixedMoment B raw7500step1 raw7500step1Labels := by
      have ha : raw7500step1 = -raw7500step0 := by apply Matrix.ext; change ∀ i j, raw7500step1 i j = -(raw7500step0 i j); unfold raw7500step1 raw7500step0; decide +kernel
      have hl : raw7500step1Labels = raw7500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw7501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw7501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7501 raw7501Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw7501 raw7501Labels = mixedMoment B raw7501step0 raw7501step0Labels := by
      have ha : raw7501step0 = (fun i j => raw7501 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7501step0 raw7501; decide +kernel
      have hl : raw7501step0Labels = raw7501Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7501 raw7501Labels permutation676 permutation2
    mixedMoment B raw7501step0 raw7501step0Labels = mixedMoment B raw7501step1 raw7501step1Labels := by
      have ha : raw7501step1 = -raw7501step0 := by apply Matrix.ext; change ∀ i j, raw7501step1 i j = -(raw7501step0 i j); unfold raw7501step1 raw7501step0; decide +kernel
      have hl : raw7501step1Labels = raw7501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw7502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw7502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7502 raw7502Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw7502 raw7502Labels = mixedMoment B raw7502step0 raw7502step0Labels := by
      have ha : raw7502step0 = (fun i j => raw7502 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7502step0 raw7502; decide +kernel
      have hl : raw7502step0Labels = raw7502Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7502 raw7502Labels permutation674 permutation2
    mixedMoment B raw7502step0 raw7502step0Labels = mixedMoment B raw7502step1 raw7502step1Labels := by
      have ha : raw7502step1 = -raw7502step0 := by apply Matrix.ext; change ∀ i j, raw7502step1 i j = -(raw7502step0 i j); unfold raw7502step1 raw7502step0; decide +kernel
      have hl : raw7502step1Labels = raw7502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw7503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw7503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7503 raw7503Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw7503 raw7503Labels = mixedMoment B raw7503step0 raw7503step0Labels := by
      have hz : ∀ j, raw7503 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7503step0 = (fun i j => raw7503 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7503step0 raw7503; decide +kernel
      have hl : raw7503step0Labels = raw7503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7503 raw7503Labels permutation520 hz
    mixedMoment B raw7503step0 raw7503step0Labels = mixedMoment B raw7503step1 raw7503step1Labels := by
      have ha : raw7503step1 = (fun i j => raw7503step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7503step1 raw7503step0; decide +kernel
      have hl : raw7503step1Labels = raw7503step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7503step0 raw7503step0Labels permutation137 permutation2
    mixedMoment B raw7503step1 raw7503step1Labels = mixedMoment B raw7503step2 raw7503step2Labels := by
      have ha : raw7503step2 = -raw7503step1 := by apply Matrix.ext; change ∀ i j, raw7503step2 i j = -(raw7503step1 i j); unfold raw7503step2 raw7503step1; decide +kernel
      have hl : raw7503step2Labels = raw7503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw7504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw7504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7504 raw7504Labels = mixedMoment B node4008 node4008Labels := by
  calc
    mixedMoment B raw7504 raw7504Labels = mixedMoment B raw7504step0 raw7504step0Labels := by
      have ha : raw7504step0 = (fun i j => raw7504 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7504step0 raw7504; decide +kernel
      have hl : raw7504step0Labels = raw7504Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7504 raw7504Labels permutation182 permutation2
    _ = mixedMoment B node4008 node4008Labels := by rfl

def raw7505 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]
def raw7505Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7505step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]
def raw7505step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7505step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw7505step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7505step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw7505step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical7505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7505 raw7505Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw7505 raw7505Labels = mixedMoment B raw7505step0 raw7505step0Labels := by
      have hz : ∀ j, raw7505 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7505step0 = (fun i j => raw7505 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7505step0 raw7505; decide +kernel
      have hl : raw7505step0Labels = raw7505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7505 raw7505Labels permutation520 hz
    mixedMoment B raw7505step0 raw7505step0Labels = mixedMoment B raw7505step1 raw7505step1Labels := by
      have ha : raw7505step1 = (fun i j => raw7505step0 (permutation134 i) (permutation0 j)) := by apply Matrix.ext; unfold raw7505step1 raw7505step0; decide +kernel
      have hl : raw7505step1Labels = raw7505step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7505step0 raw7505step0Labels permutation134 permutation0
    mixedMoment B raw7505step1 raw7505step1Labels = mixedMoment B raw7505step2 raw7505step2Labels := by
      have ha : raw7505step2 = -raw7505step1 := by apply Matrix.ext; change ∀ i j, raw7505step2 i j = -(raw7505step1 i j); unfold raw7505step2 raw7505step1; decide +kernel
      have hl : raw7505step2Labels = raw7505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw7506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7506 raw7506Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw7506 raw7506Labels = mixedMoment B raw7506step0 raw7506step0Labels := by
      have ha : raw7506step0 = (fun i j => raw7506 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7506step0 raw7506; decide +kernel
      have hl : raw7506step0Labels = raw7506Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7506 raw7506Labels permutation184 permutation2
    _ = mixedMoment B node1383 node1383Labels := by rfl

def raw7507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7507 raw7507Labels = mixedMoment B node1392 node1392Labels := by
  calc
    mixedMoment B raw7507 raw7507Labels = mixedMoment B raw7507step0 raw7507step0Labels := by
      have ha : raw7507step0 = (fun i j => raw7507 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7507step0 raw7507; decide +kernel
      have hl : raw7507step0Labels = raw7507Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7507 raw7507Labels permutation200 permutation2
    _ = mixedMoment B node1392 node1392Labels := by rfl

def raw7508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7508 raw7508Labels = mixedMoment B node1392 node1392Labels := by
  calc
    mixedMoment B raw7508 raw7508Labels = mixedMoment B raw7508step0 raw7508step0Labels := by
      have ha : raw7508step0 = (fun i j => raw7508 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7508step0 raw7508; decide +kernel
      have hl : raw7508step0Labels = raw7508Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7508 raw7508Labels permutation176 permutation2
    _ = mixedMoment B node1392 node1392Labels := by rfl

def raw7509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7509 raw7509Labels = mixedMoment B node1380 node1380Labels := by
  calc
    mixedMoment B raw7509 raw7509Labels = mixedMoment B raw7509step0 raw7509step0Labels := by
      have ha : raw7509step0 = (fun i j => raw7509 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7509step0 raw7509; decide +kernel
      have hl : raw7509step0Labels = raw7509Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7509 raw7509Labels permutation182 permutation2
    _ = mixedMoment B node1380 node1380Labels := by rfl

def raw7510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7510 raw7510Labels = mixedMoment B node1378 node1378Labels := by
  calc
    mixedMoment B raw7510 raw7510Labels = mixedMoment B raw7510step0 raw7510step0Labels := by
      have ha : raw7510step0 = (fun i j => raw7510 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7510step0 raw7510; decide +kernel
      have hl : raw7510step0Labels = raw7510Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7510 raw7510Labels permutation182 permutation2
    _ = mixedMoment B node1378 node1378Labels := by rfl

def raw7511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7511 raw7511Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw7511 raw7511Labels = mixedMoment B raw7511step0 raw7511step0Labels := by
      have ha : raw7511step0 = (fun i j => raw7511 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7511step0 raw7511; decide +kernel
      have hl : raw7511step0Labels = raw7511Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7511 raw7511Labels permutation184 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw7512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7512 raw7512Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw7512 raw7512Labels = mixedMoment B raw7512step0 raw7512step0Labels := by
      have ha : raw7512step0 = (fun i j => raw7512 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7512step0 raw7512; decide +kernel
      have hl : raw7512step0Labels = raw7512Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7512 raw7512Labels permutation208 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw7513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7513 raw7513Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw7513 raw7513Labels = mixedMoment B raw7513step0 raw7513step0Labels := by
      have hz : ∀ j, raw7513 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7513step0 = (fun i j => raw7513 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7513step0 raw7513; decide +kernel
      have hl : raw7513step0Labels = raw7513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7513 raw7513Labels permutation520 hz
    mixedMoment B raw7513step0 raw7513step0Labels = mixedMoment B raw7513step1 raw7513step1Labels := by
      have ha : raw7513step1 = (fun i j => raw7513step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7513step1 raw7513step0; decide +kernel
      have hl : raw7513step1Labels = raw7513step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7513step0 raw7513step0Labels permutation40 permutation2
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw7514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7514 raw7514Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw7514 raw7514Labels = mixedMoment B raw7514step0 raw7514step0Labels := by
      have ha : raw7514step0 = (fun i j => raw7514 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7514step0 raw7514; decide +kernel
      have hl : raw7514step0Labels = raw7514Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7514 raw7514Labels permutation184 permutation2
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw7515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7515 raw7515Labels = mixedMoment B node3013 node3013Labels := by
  calc
    mixedMoment B raw7515 raw7515Labels = mixedMoment B raw7515step0 raw7515step0Labels := by
      have ha : raw7515step0 = (fun i j => raw7515 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7515step0 raw7515; decide +kernel
      have hl : raw7515step0Labels = raw7515Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7515 raw7515Labels permutation158 permutation2
    _ = mixedMoment B node3013 node3013Labels := by rfl

def raw7516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7516 raw7516Labels = mixedMoment B node3013 node3013Labels := by
  calc
    _ = mixedMoment B node3013 node3013Labels := by rfl

def raw7517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7517 raw7517Labels = mixedMoment B node3012 node3012Labels := by
  calc
    _ = mixedMoment B node3012 node3012Labels := by rfl

def raw7518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 2, 1]]
def raw7518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw7518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7518 raw7518Labels = mixedMoment B node2562 node2562Labels := by
  calc
    mixedMoment B raw7518 raw7518Labels = mixedMoment B raw7518step0 raw7518step0Labels := by
      have ha : raw7518step0 = (fun i j => raw7518 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7518step0 raw7518; decide +kernel
      have hl : raw7518step0Labels = raw7518Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7518 raw7518Labels permutation682 permutation2
    mixedMoment B raw7518step0 raw7518step0Labels = mixedMoment B raw7518step1 raw7518step1Labels := by
      have ha : raw7518step1 = -raw7518step0 := by apply Matrix.ext; change ∀ i j, raw7518step1 i j = -(raw7518step0 i j); unfold raw7518step1 raw7518step0; decide +kernel
      have hl : raw7518step1Labels = raw7518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2562 node2562Labels := by rfl

def raw7519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7519 raw7519Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw7519 raw7519Labels = mixedMoment B raw7519step0 raw7519step0Labels := by
      have ha : raw7519step0 = (fun i j => raw7519 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7519step0 raw7519; decide +kernel
      have hl : raw7519step0Labels = raw7519Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7519 raw7519Labels permutation176 permutation2
    _ = mixedMoment B node2933 node2933Labels := by rfl

def raw7520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7520 raw7520Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw7520 raw7520Labels = mixedMoment B raw7520step0 raw7520step0Labels := by
      have ha : raw7520step0 = (fun i j => raw7520 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7520step0 raw7520; decide +kernel
      have hl : raw7520step0Labels = raw7520Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7520 raw7520Labels permutation182 permutation2
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw7521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7521 raw7521Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw7521 raw7521Labels = mixedMoment B raw7521step0 raw7521step0Labels := by
      have ha : raw7521step0 = (fun i j => raw7521 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7521step0 raw7521; decide +kernel
      have hl : raw7521step0Labels = raw7521Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7521 raw7521Labels permutation676 permutation2
    mixedMoment B raw7521step0 raw7521step0Labels = mixedMoment B raw7521step1 raw7521step1Labels := by
      have ha : raw7521step1 = -raw7521step0 := by apply Matrix.ext; change ∀ i j, raw7521step1 i j = -(raw7521step0 i j); unfold raw7521step1 raw7521step0; decide +kernel
      have hl : raw7521step1Labels = raw7521step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw7522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7522 raw7522Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw7522 raw7522Labels = mixedMoment B raw7522step0 raw7522step0Labels := by
      have ha : raw7522step0 = (fun i j => raw7522 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7522step0 raw7522; decide +kernel
      have hl : raw7522step0Labels = raw7522Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7522 raw7522Labels permutation206 permutation2
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw7523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw7523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7523 raw7523Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw7523 raw7523Labels = mixedMoment B raw7523step0 raw7523step0Labels := by
      have ha : raw7523step0 = (fun i j => raw7523 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7523step0 raw7523; decide +kernel
      have hl : raw7523step0Labels = raw7523Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7523 raw7523Labels permutation183 permutation2
    _ = mixedMoment B node3066 node3066Labels := by rfl

def raw7524 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7524step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7524 raw7524Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw7524 raw7524Labels = mixedMoment B raw7524step0 raw7524step0Labels := by
      have ha : raw7524step0 = (fun i j => raw7524 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7524step0 raw7524; decide +kernel
      have hl : raw7524step0Labels = raw7524Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7524 raw7524Labels permutation182 permutation7
    mixedMoment B raw7524step0 raw7524step0Labels = mixedMoment B raw7524step1 raw7524step1Labels := by
      have ha : raw7524step1 = raw7524step0 := by apply Matrix.ext; unfold raw7524step1 raw7524step0; decide +kernel
      have hl : raw7524step0Labels = labelEmbedding10 ∘ raw7524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7524step0 raw7524step0Labels raw7524step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw7525 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7525step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7525 raw7525Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw7525 raw7525Labels = mixedMoment B raw7525step0 raw7525step0Labels := by
      have hz : ∀ j, raw7525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7525step0 = (fun i j => raw7525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7525step0 raw7525; decide +kernel
      have hl : raw7525step0Labels = raw7525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7525 raw7525Labels permutation434 hz
    mixedMoment B raw7525step0 raw7525step0Labels = mixedMoment B raw7525step1 raw7525step1Labels := by
      have ha : raw7525step1 = (fun i j => raw7525step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7525step1 raw7525step0; decide +kernel
      have hl : raw7525step1Labels = raw7525step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7525step0 raw7525step0Labels permutation38 permutation7
    mixedMoment B raw7525step1 raw7525step1Labels = mixedMoment B raw7525step2 raw7525step2Labels := by
      have ha : raw7525step2 = raw7525step1 := by apply Matrix.ext; unfold raw7525step2 raw7525step1; decide +kernel
      have hl : raw7525step1Labels = labelEmbedding10 ∘ raw7525step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7525step1 raw7525step1Labels raw7525step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw7526 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw7526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7526 raw7526Labels = mixedMoment B node5133 node5133Labels := by
  calc
    mixedMoment B raw7526 raw7526Labels = mixedMoment B raw7526step0 raw7526step0Labels := by
      have ha : raw7526step0 = (fun i j => raw7526 (permutation620 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7526step0 raw7526; decide +kernel
      have hl : raw7526step0Labels = raw7526Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7526 raw7526Labels permutation620 permutation2
    _ = mixedMoment B node5133 node5133Labels := by rfl

def raw7527 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7527step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7527step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7527 raw7527Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw7527 raw7527Labels = mixedMoment B raw7527step0 raw7527step0Labels := by
      have hz : ∀ j, raw7527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7527step0 = (fun i j => raw7527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7527step0 raw7527; decide +kernel
      have hl : raw7527step0Labels = raw7527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7527 raw7527Labels permutation434 hz
    mixedMoment B raw7527step0 raw7527step0Labels = mixedMoment B raw7527step1 raw7527step1Labels := by
      have hz : ∀ j, raw7527step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7527step1 = (fun i j => raw7527step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7527step1 raw7527step0; decide +kernel
      have hl : raw7527step1Labels = raw7527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7527step0 raw7527step0Labels permutation56 hz
    mixedMoment B raw7527step1 raw7527step1Labels = mixedMoment B raw7527step2 raw7527step2Labels := by
      have ha : raw7527step2 = (fun i j => raw7527step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7527step2 raw7527step1; decide +kernel
      have hl : raw7527step2Labels = raw7527step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7527step1 raw7527step1Labels permutation8 permutation6
    mixedMoment B raw7527step2 raw7527step2Labels = mixedMoment B raw7527step3 raw7527step3Labels := by
      have ha : raw7527step3 = raw7527step2 := by apply Matrix.ext; unfold raw7527step3 raw7527step2; decide +kernel
      have hl : raw7527step2Labels = labelEmbedding9 ∘ raw7527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7527step2 raw7527step2Labels raw7527step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw7528 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7528 raw7528Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw7528 raw7528Labels = mixedMoment B raw7528step0 raw7528step0Labels := by
      have hz : ∀ j, raw7528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7528step0 = (fun i j => raw7528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7528step0 raw7528; decide +kernel
      have hl : raw7528step0Labels = raw7528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7528 raw7528Labels permutation265 hz
    mixedMoment B raw7528step0 raw7528step0Labels = mixedMoment B raw7528step1 raw7528step1Labels := by
      have ha : raw7528step1 = (fun i j => raw7528step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7528step1 raw7528step0; decide +kernel
      have hl : raw7528step1Labels = raw7528step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7528step0 raw7528step0Labels permutation149 permutation2
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw7529 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw7529step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7529step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7529 raw7529Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw7529 raw7529Labels = mixedMoment B raw7529step0 raw7529step0Labels := by
      have ha : raw7529step0 = (fun i j => raw7529 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7529step0 raw7529; decide +kernel
      have hl : raw7529step0Labels = raw7529Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7529 raw7529Labels permutation173 permutation4
    mixedMoment B raw7529step0 raw7529step0Labels = mixedMoment B raw7529step1 raw7529step1Labels := by
      have ha : raw7529step1 = -raw7529step0 := by apply Matrix.ext; change ∀ i j, raw7529step1 i j = -(raw7529step0 i j); unfold raw7529step1 raw7529step0; decide +kernel
      have hl : raw7529step1Labels = raw7529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7529step1 raw7529step1Labels = mixedMoment B raw7529step2 raw7529step2Labels := by
      have ha : raw7529step2 = raw7529step1 := by apply Matrix.ext; unfold raw7529step2 raw7529step1; decide +kernel
      have hl : raw7529step1Labels = labelEmbedding7 ∘ raw7529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7529step1 raw7529step1Labels raw7529step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw7530 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7530step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7530 raw7530Labels = mixedMoment B node5224 node5224Labels := by
  calc
    mixedMoment B raw7530 raw7530Labels = mixedMoment B raw7530step0 raw7530step0Labels := by
      have ha : raw7530step0 = (fun i j => raw7530 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7530step0 raw7530; decide +kernel
      have hl : raw7530step0Labels = raw7530Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7530 raw7530Labels permutation158 permutation6
    mixedMoment B raw7530step0 raw7530step0Labels = mixedMoment B raw7530step1 raw7530step1Labels := by
      have ha : raw7530step1 = raw7530step0 := by apply Matrix.ext; unfold raw7530step1 raw7530step0; decide +kernel
      have hl : raw7530step0Labels = labelEmbedding9 ∘ raw7530step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7530step0 raw7530step0Labels raw7530step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5224 node5224Labels := by rfl

def raw7531 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7531step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7531step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7531 raw7531Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw7531 raw7531Labels = mixedMoment B raw7531step0 raw7531step0Labels := by
      have hz : ∀ j, raw7531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7531step0 = (fun i j => raw7531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7531step0 raw7531; decide +kernel
      have hl : raw7531step0Labels = raw7531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7531 raw7531Labels permutation434 hz
    mixedMoment B raw7531step0 raw7531step0Labels = mixedMoment B raw7531step1 raw7531step1Labels := by
      have ha : raw7531step1 = (fun i j => raw7531step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7531step1 raw7531step0; decide +kernel
      have hl : raw7531step1Labels = raw7531step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7531step0 raw7531step0Labels permutation32 permutation6
    mixedMoment B raw7531step1 raw7531step1Labels = mixedMoment B raw7531step2 raw7531step2Labels := by
      have ha : raw7531step2 = raw7531step1 := by apply Matrix.ext; unfold raw7531step2 raw7531step1; decide +kernel
      have hl : raw7531step1Labels = labelEmbedding9 ∘ raw7531step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7531step1 raw7531step1Labels raw7531step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw7532 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw7532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7532 raw7532Labels = mixedMoment B node5136 node5136Labels := by
  calc
    mixedMoment B raw7532 raw7532Labels = mixedMoment B raw7532step0 raw7532step0Labels := by
      have ha : raw7532step0 = (fun i j => raw7532 (permutation621 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7532step0 raw7532; decide +kernel
      have hl : raw7532step0Labels = raw7532Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7532 raw7532Labels permutation621 permutation2
    _ = mixedMoment B node5136 node5136Labels := by rfl

def raw7533 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7533 raw7533Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw7533 raw7533Labels = mixedMoment B raw7533step0 raw7533step0Labels := by
      have ha : raw7533step0 = (fun i j => raw7533 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7533step0 raw7533; decide +kernel
      have hl : raw7533step0Labels = raw7533Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7533 raw7533Labels permutation152 permutation6
    _ = mixedMoment B node3030 node3030Labels := by rfl

def raw7534 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7534 raw7534Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw7534 raw7534Labels = mixedMoment B raw7534step0 raw7534step0Labels := by
      have hz : ∀ j, raw7534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7534step0 = (fun i j => raw7534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7534step0 raw7534; decide +kernel
      have hl : raw7534step0Labels = raw7534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7534 raw7534Labels permutation434 hz
    mixedMoment B raw7534step0 raw7534step0Labels = mixedMoment B raw7534step1 raw7534step1Labels := by
      have ha : raw7534step1 = (fun i j => raw7534step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7534step1 raw7534step0; decide +kernel
      have hl : raw7534step1Labels = raw7534step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7534step0 raw7534step0Labels permutation32 permutation6
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw7535 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw7535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7535 raw7535Labels = mixedMoment B node2940 node2940Labels := by
  calc
    mixedMoment B raw7535 raw7535Labels = mixedMoment B raw7535step0 raw7535step0Labels := by
      have ha : raw7535step0 = (fun i j => raw7535 (permutation620 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7535step0 raw7535; decide +kernel
      have hl : raw7535step0Labels = raw7535Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7535 raw7535Labels permutation620 permutation3
    _ = mixedMoment B node2940 node2940Labels := by rfl

def raw7536 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7536step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7536 raw7536Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw7536 raw7536Labels = mixedMoment B raw7536step0 raw7536step0Labels := by
      have hz : ∀ j, raw7536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7536step0 = (fun i j => raw7536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7536step0 raw7536; decide +kernel
      have hl : raw7536step0Labels = raw7536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7536 raw7536Labels permutation434 hz
    mixedMoment B raw7536step0 raw7536step0Labels = mixedMoment B raw7536step1 raw7536step1Labels := by
      have hz : ∀ j, raw7536step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7536step1 = (fun i j => raw7536step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7536step1 raw7536step0; decide +kernel
      have hl : raw7536step1Labels = raw7536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7536step0 raw7536step0Labels permutation56 hz
    mixedMoment B raw7536step1 raw7536step1Labels = mixedMoment B raw7536step2 raw7536step2Labels := by
      have ha : raw7536step2 = (fun i j => raw7536step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7536step2 raw7536step1; decide +kernel
      have hl : raw7536step2Labels = raw7536step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7536step1 raw7536step1Labels permutation8 permutation6
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw7537 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw7537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7537 raw7537Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw7537 raw7537Labels = mixedMoment B raw7537step0 raw7537step0Labels := by
      have hz : ∀ j, raw7537 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7537step0 = (fun i j => raw7537 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7537step0 raw7537; decide +kernel
      have hl : raw7537step0Labels = raw7537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7537 raw7537Labels permutation265 hz
    mixedMoment B raw7537step0 raw7537step0Labels = mixedMoment B raw7537step1 raw7537step1Labels := by
      have ha : raw7537step1 = (fun i j => raw7537step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7537step1 raw7537step0; decide +kernel
      have hl : raw7537step1Labels = raw7537step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7537step0 raw7537step0Labels permutation32 permutation6
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw7538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7538 raw7538Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw7538 raw7538Labels = mixedMoment B raw7538step0 raw7538step0Labels := by
      have ha : raw7538step0 = (fun i j => raw7538 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7538step0 raw7538; decide +kernel
      have hl : raw7538step0Labels = raw7538Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7538 raw7538Labels permutation158 permutation6
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw7539 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7539 raw7539Labels = mixedMoment B node2666 node2666Labels := by
  calc
    mixedMoment B raw7539 raw7539Labels = mixedMoment B raw7539step0 raw7539step0Labels := by
      have ha : raw7539step0 = (fun i j => raw7539 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7539step0 raw7539; decide +kernel
      have hl : raw7539step0Labels = raw7539Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7539 raw7539Labels permutation158 permutation6
    _ = mixedMoment B node2666 node2666Labels := by rfl

def raw7540 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7540 raw7540Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw7540 raw7540Labels = mixedMoment B raw7540step0 raw7540step0Labels := by
      have hz : ∀ j, raw7540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7540step0 = (fun i j => raw7540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7540step0 raw7540; decide +kernel
      have hl : raw7540step0Labels = raw7540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7540 raw7540Labels permutation434 hz
    mixedMoment B raw7540step0 raw7540step0Labels = mixedMoment B raw7540step1 raw7540step1Labels := by
      have ha : raw7540step1 = (fun i j => raw7540step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7540step1 raw7540step0; decide +kernel
      have hl : raw7540step1Labels = raw7540step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7540step0 raw7540step0Labels permutation32 permutation6
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw7541 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7541 raw7541Labels = mixedMoment B node2715 node2715Labels := by
  calc
    mixedMoment B raw7541 raw7541Labels = mixedMoment B raw7541step0 raw7541step0Labels := by
      have ha : raw7541step0 = (fun i j => raw7541 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7541step0 raw7541; decide +kernel
      have hl : raw7541step0Labels = raw7541Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7541 raw7541Labels permutation158 permutation6
    _ = mixedMoment B node2715 node2715Labels := by rfl

def raw7542 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7542 raw7542Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw7542 raw7542Labels = mixedMoment B raw7542step0 raw7542step0Labels := by
      have ha : raw7542step0 = (fun i j => raw7542 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7542step0 raw7542; decide +kernel
      have hl : raw7542step0Labels = raw7542Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7542 raw7542Labels permutation182 permutation7
    mixedMoment B raw7542step0 raw7542step0Labels = mixedMoment B raw7542step1 raw7542step1Labels := by
      have ha : raw7542step1 = raw7542step0 := by apply Matrix.ext; unfold raw7542step1 raw7542step0; decide +kernel
      have hl : raw7542step0Labels = labelEmbedding1 ∘ raw7542step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7542step0 raw7542step0Labels raw7542step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw7543 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7543 raw7543Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw7543 raw7543Labels = mixedMoment B raw7543step0 raw7543step0Labels := by
      have hz : ∀ j, raw7543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7543step0 = (fun i j => raw7543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7543step0 raw7543; decide +kernel
      have hl : raw7543step0Labels = raw7543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7543 raw7543Labels permutation434 hz
    mixedMoment B raw7543step0 raw7543step0Labels = mixedMoment B raw7543step1 raw7543step1Labels := by
      have ha : raw7543step1 = (fun i j => raw7543step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7543step1 raw7543step0; decide +kernel
      have hl : raw7543step1Labels = raw7543step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7543step0 raw7543step0Labels permutation38 permutation7
    mixedMoment B raw7543step1 raw7543step1Labels = mixedMoment B raw7543step2 raw7543step2Labels := by
      have ha : raw7543step2 = raw7543step1 := by apply Matrix.ext; unfold raw7543step2 raw7543step1; decide +kernel
      have hl : raw7543step1Labels = labelEmbedding1 ∘ raw7543step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7543step1 raw7543step1Labels raw7543step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw7544 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7544 raw7544Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw7544 raw7544Labels = mixedMoment B raw7544step0 raw7544step0Labels := by
      have ha : raw7544step0 = (fun i j => raw7544 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7544step0 raw7544; decide +kernel
      have hl : raw7544step0Labels = raw7544Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7544 raw7544Labels permutation182 permutation7
    mixedMoment B raw7544step0 raw7544step0Labels = mixedMoment B raw7544step1 raw7544step1Labels := by
      have ha : raw7544step1 = raw7544step0 := by apply Matrix.ext; unfold raw7544step1 raw7544step0; decide +kernel
      have hl : raw7544step0Labels = labelEmbedding1 ∘ raw7544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7544step0 raw7544step0Labels raw7544step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2693 node2693Labels := by rfl

def raw7545 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7545step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7545step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7545step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7545 raw7545Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw7545 raw7545Labels = mixedMoment B raw7545step0 raw7545step0Labels := by
      have hz : ∀ j, raw7545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7545step0 = (fun i j => raw7545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7545step0 raw7545; decide +kernel
      have hl : raw7545step0Labels = raw7545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7545 raw7545Labels permutation434 hz
    mixedMoment B raw7545step0 raw7545step0Labels = mixedMoment B raw7545step1 raw7545step1Labels := by
      have hz : ∀ j, raw7545step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7545step1 = (fun i j => raw7545step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7545step1 raw7545step0; decide +kernel
      have hl : raw7545step1Labels = raw7545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7545step0 raw7545step0Labels permutation56 hz
    mixedMoment B raw7545step1 raw7545step1Labels = mixedMoment B raw7545step2 raw7545step2Labels := by
      have ha : raw7545step2 = (fun i j => raw7545step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7545step2 raw7545step1; decide +kernel
      have hl : raw7545step2Labels = raw7545step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7545step1 raw7545step1Labels permutation8 permutation7
    mixedMoment B raw7545step2 raw7545step2Labels = mixedMoment B raw7545step3 raw7545step3Labels := by
      have ha : raw7545step3 = raw7545step2 := by apply Matrix.ext; unfold raw7545step3 raw7545step2; decide +kernel
      have hl : raw7545step2Labels = labelEmbedding1 ∘ raw7545step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7545step2 raw7545step2Labels raw7545step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw7546 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw7546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw7546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7546 raw7546Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw7546 raw7546Labels = mixedMoment B raw7546step0 raw7546step0Labels := by
      have hz : ∀ j, raw7546 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7546step0 = (fun i j => raw7546 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7546step0 raw7546; decide +kernel
      have hl : raw7546step0Labels = raw7546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7546 raw7546Labels permutation265 hz
    mixedMoment B raw7546step0 raw7546step0Labels = mixedMoment B raw7546step1 raw7546step1Labels := by
      have ha : raw7546step1 = (fun i j => raw7546step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7546step1 raw7546step0; decide +kernel
      have hl : raw7546step1Labels = raw7546step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7546step0 raw7546step0Labels permutation32 permutation7
    mixedMoment B raw7546step1 raw7546step1Labels = mixedMoment B raw7546step2 raw7546step2Labels := by
      have ha : raw7546step2 = raw7546step1 := by apply Matrix.ext; unfold raw7546step2 raw7546step1; decide +kernel
      have hl : raw7546step1Labels = labelEmbedding1 ∘ raw7546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7546step1 raw7546step1Labels raw7546step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw7547 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7547Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7547step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7547step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7547step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7547 raw7547Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw7547 raw7547Labels = mixedMoment B raw7547step0 raw7547step0Labels := by
      have ha : raw7547step0 = (fun i j => raw7547 (permutation175 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7547step0 raw7547; decide +kernel
      have hl : raw7547step0Labels = raw7547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7547 raw7547Labels permutation175 permutation5
    mixedMoment B raw7547step0 raw7547step0Labels = mixedMoment B raw7547step1 raw7547step1Labels := by
      have ha : raw7547step1 = -raw7547step0 := by apply Matrix.ext; change ∀ i j, raw7547step1 i j = -(raw7547step0 i j); unfold raw7547step1 raw7547step0; decide +kernel
      have hl : raw7547step1Labels = raw7547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7547step1 raw7547step1Labels = mixedMoment B raw7547step2 raw7547step2Labels := by
      have ha : raw7547step2 = raw7547step1 := by apply Matrix.ext; unfold raw7547step2 raw7547step1; decide +kernel
      have hl : raw7547step1Labels = labelEmbedding1 ∘ raw7547step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7547step1 raw7547step1Labels raw7547step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3196 node3196Labels := by rfl

def raw7548 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7548 raw7548Labels = mixedMoment B node3018 node3018Labels := by
  calc
    mixedMoment B raw7548 raw7548Labels = mixedMoment B raw7548step0 raw7548step0Labels := by
      have ha : raw7548step0 = (fun i j => raw7548 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7548step0 raw7548; decide +kernel
      have hl : raw7548step0Labels = raw7548Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7548 raw7548Labels permutation182 permutation7
    mixedMoment B raw7548step0 raw7548step0Labels = mixedMoment B raw7548step1 raw7548step1Labels := by
      have ha : raw7548step1 = raw7548step0 := by apply Matrix.ext; unfold raw7548step1 raw7548step0; decide +kernel
      have hl : raw7548step0Labels = labelEmbedding1 ∘ raw7548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7548step0 raw7548step0Labels raw7548step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3018 node3018Labels := by rfl

def raw7549 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7549Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7549step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7549 raw7549Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw7549 raw7549Labels = mixedMoment B raw7549step0 raw7549step0Labels := by
      have hz : ∀ j, raw7549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7549step0 = (fun i j => raw7549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7549step0 raw7549; decide +kernel
      have hl : raw7549step0Labels = raw7549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7549 raw7549Labels permutation434 hz
    mixedMoment B raw7549step0 raw7549step0Labels = mixedMoment B raw7549step1 raw7549step1Labels := by
      have ha : raw7549step1 = (fun i j => raw7549step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7549step1 raw7549step0; decide +kernel
      have hl : raw7549step1Labels = raw7549step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7549step0 raw7549step0Labels permutation38 permutation7
    mixedMoment B raw7549step1 raw7549step1Labels = mixedMoment B raw7549step2 raw7549step2Labels := by
      have ha : raw7549step2 = raw7549step1 := by apply Matrix.ext; unfold raw7549step2 raw7549step1; decide +kernel
      have hl : raw7549step1Labels = labelEmbedding1 ∘ raw7549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7549step1 raw7549step1Labels raw7549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw7550 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7550 raw7550Labels = mixedMoment B node3015 node3015Labels := by
  calc
    mixedMoment B raw7550 raw7550Labels = mixedMoment B raw7550step0 raw7550step0Labels := by
      have ha : raw7550step0 = (fun i j => raw7550 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7550step0 raw7550; decide +kernel
      have hl : raw7550step0Labels = raw7550Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7550 raw7550Labels permutation182 permutation7
    mixedMoment B raw7550step0 raw7550step0Labels = mixedMoment B raw7550step1 raw7550step1Labels := by
      have ha : raw7550step1 = raw7550step0 := by apply Matrix.ext; unfold raw7550step1 raw7550step0; decide +kernel
      have hl : raw7550step0Labels = labelEmbedding1 ∘ raw7550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7550step0 raw7550step0Labels raw7550step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3015 node3015Labels := by rfl

def raw7551 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw7551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7551 raw7551Labels = mixedMoment B node3488 node3488Labels := by
  calc
    mixedMoment B raw7551 raw7551Labels = mixedMoment B raw7551step0 raw7551step0Labels := by
      have ha : raw7551step0 = (fun i j => raw7551 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7551step0 raw7551; decide +kernel
      have hl : raw7551step0Labels = raw7551Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7551 raw7551Labels permutation184 permutation2
    mixedMoment B raw7551step0 raw7551step0Labels = mixedMoment B raw7551step1 raw7551step1Labels := by
      have ha : raw7551step1 = -raw7551step0 := by apply Matrix.ext; change ∀ i j, raw7551step1 i j = -(raw7551step0 i j); unfold raw7551step1 raw7551step0; decide +kernel
      have hl : raw7551step1Labels = raw7551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3488 node3488Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
