import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14464step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14464 raw14464Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw14464 raw14464Labels = mixedMoment B raw14464step0 raw14464step0Labels := by
      have ha : raw14464step0 = (fun i j => raw14464 (permutation559 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14464step0 raw14464; decide +kernel
      have hl : raw14464step0Labels = raw14464Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14464 raw14464Labels permutation559 permutation6
    mixedMoment B raw14464step0 raw14464step0Labels = mixedMoment B raw14464step1 raw14464step1Labels := by
      have ha : raw14464step1 = raw14464step0 := by apply Matrix.ext; unfold raw14464step1 raw14464step0; decide +kernel
      have hl : raw14464step0Labels = labelEmbedding9 ∘ raw14464step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14464step0 raw14464step0Labels raw14464step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw14465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14465 raw14465Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw14465 raw14465Labels = mixedMoment B raw14465step0 raw14465step0Labels := by
      have hz : ∀ j, raw14465 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14465step0 = (fun i j => raw14465 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14465step0 raw14465; decide +kernel
      have hl : raw14465step0Labels = raw14465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14465 raw14465Labels permutation265 hz
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw14466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14466 raw14466Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw14466 raw14466Labels = mixedMoment B raw14466step0 raw14466step0Labels := by
      have hz : ∀ j, raw14466 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14466step0 = (fun i j => raw14466 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14466step0 raw14466; decide +kernel
      have hl : raw14466step0Labels = raw14466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14466 raw14466Labels permutation265 hz
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw14467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14467step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14467step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14467 raw14467Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw14467 raw14467Labels = mixedMoment B raw14467step0 raw14467step0Labels := by
      have hz : ∀ j, raw14467 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14467step0 = (fun i j => raw14467 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14467step0 raw14467; decide +kernel
      have hl : raw14467step0Labels = raw14467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14467 raw14467Labels permutation265 hz
    mixedMoment B raw14467step0 raw14467step0Labels = mixedMoment B raw14467step1 raw14467step1Labels := by
      have ha : raw14467step1 = (fun i j => raw14467step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14467step1 raw14467step0; decide +kernel
      have hl : raw14467step1Labels = raw14467step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14467step0 raw14467step0Labels permutation135 permutation5
    mixedMoment B raw14467step1 raw14467step1Labels = mixedMoment B raw14467step2 raw14467step2Labels := by
      have ha : raw14467step2 = raw14467step1 := by apply Matrix.ext; unfold raw14467step2 raw14467step1; decide +kernel
      have hl : raw14467step1Labels = labelEmbedding8 ∘ raw14467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14467step1 raw14467step1Labels raw14467step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw14468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14468step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14468step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14468step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14468 raw14468Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw14468 raw14468Labels = mixedMoment B raw14468step0 raw14468step0Labels := by
      have hz : ∀ j, raw14468 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14468step0 = (fun i j => raw14468 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14468step0 raw14468; decide +kernel
      have hl : raw14468step0Labels = raw14468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14468 raw14468Labels permutation265 hz
    mixedMoment B raw14468step0 raw14468step0Labels = mixedMoment B raw14468step1 raw14468step1Labels := by
      have ha : raw14468step1 = (fun i j => raw14468step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14468step1 raw14468step0; decide +kernel
      have hl : raw14468step1Labels = raw14468step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14468step0 raw14468step0Labels permutation116 permutation4
    mixedMoment B raw14468step1 raw14468step1Labels = mixedMoment B raw14468step2 raw14468step2Labels := by
      have ha : raw14468step2 = -raw14468step1 := by apply Matrix.ext; change ∀ i j, raw14468step2 i j = -(raw14468step1 i j); unfold raw14468step2 raw14468step1; decide +kernel
      have hl : raw14468step2Labels = raw14468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14468step2 raw14468step2Labels = mixedMoment B raw14468step3 raw14468step3Labels := by
      have ha : raw14468step3 = raw14468step2 := by apply Matrix.ext; unfold raw14468step3 raw14468step2; decide +kernel
      have hl : raw14468step2Labels = labelEmbedding7 ∘ raw14468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14468step2 raw14468step2Labels raw14468step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw14469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14469step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14469step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14469step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14469step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14469 raw14469Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw14469 raw14469Labels = mixedMoment B raw14469step0 raw14469step0Labels := by
      have hz : ∀ j, raw14469 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14469step0 = (fun i j => raw14469 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14469step0 raw14469; decide +kernel
      have hl : raw14469step0Labels = raw14469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14469 raw14469Labels permutation265 hz
    mixedMoment B raw14469step0 raw14469step0Labels = mixedMoment B raw14469step1 raw14469step1Labels := by
      have ha : raw14469step1 = (fun i j => raw14469step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14469step1 raw14469step0; decide +kernel
      have hl : raw14469step1Labels = raw14469step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14469step0 raw14469step0Labels permutation36 permutation7
    mixedMoment B raw14469step1 raw14469step1Labels = mixedMoment B raw14469step2 raw14469step2Labels := by
      have ha : raw14469step2 = -raw14469step1 := by apply Matrix.ext; change ∀ i j, raw14469step2 i j = -(raw14469step1 i j); unfold raw14469step2 raw14469step1; decide +kernel
      have hl : raw14469step2Labels = raw14469step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14469step2 raw14469step2Labels = mixedMoment B raw14469step3 raw14469step3Labels := by
      have ha : raw14469step3 = raw14469step2 := by apply Matrix.ext; unfold raw14469step3 raw14469step2; decide +kernel
      have hl : raw14469step2Labels = labelEmbedding10 ∘ raw14469step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14469step2 raw14469step2Labels raw14469step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw14470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14470 raw14470Labels = mixedMoment B node5146 node5146Labels := by
  calc
    mixedMoment B raw14470 raw14470Labels = mixedMoment B raw14470step0 raw14470step0Labels := by
      have ha : raw14470step0 = (fun i j => raw14470 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14470step0 raw14470; decide +kernel
      have hl : raw14470step0Labels = raw14470Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14470 raw14470Labels permutation158 permutation2
    _ = mixedMoment B node5146 node5146Labels := by rfl

def raw14471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14471step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14471 raw14471Labels = mixedMoment B node5357 node5357Labels := by
  calc
    mixedMoment B raw14471 raw14471Labels = mixedMoment B raw14471step0 raw14471step0Labels := by
      have ha : raw14471step0 = (fun i j => raw14471 (permutation628 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14471step0 raw14471; decide +kernel
      have hl : raw14471step0Labels = raw14471Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14471 raw14471Labels permutation628 permutation5
    mixedMoment B raw14471step0 raw14471step0Labels = mixedMoment B raw14471step1 raw14471step1Labels := by
      have ha : raw14471step1 = raw14471step0 := by apply Matrix.ext; unfold raw14471step1 raw14471step0; decide +kernel
      have hl : raw14471step0Labels = labelEmbedding8 ∘ raw14471step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14471step0 raw14471step0Labels raw14471step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5357 node5357Labels := by rfl

def raw14472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14472step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14472 raw14472Labels = mixedMoment B node5358 node5358Labels := by
  calc
    mixedMoment B raw14472 raw14472Labels = mixedMoment B raw14472step0 raw14472step0Labels := by
      have ha : raw14472step0 = (fun i j => raw14472 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14472step0 raw14472; decide +kernel
      have hl : raw14472step0Labels = raw14472Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14472 raw14472Labels permutation627 permutation5
    mixedMoment B raw14472step0 raw14472step0Labels = mixedMoment B raw14472step1 raw14472step1Labels := by
      have ha : raw14472step1 = raw14472step0 := by apply Matrix.ext; unfold raw14472step1 raw14472step0; decide +kernel
      have hl : raw14472step0Labels = labelEmbedding8 ∘ raw14472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14472step0 raw14472step0Labels raw14472step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5358 node5358Labels := by rfl

def raw14473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14473step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14473 raw14473Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw14473 raw14473Labels = mixedMoment B raw14473step0 raw14473step0Labels := by
      have ha : raw14473step0 = (fun i j => raw14473 (permutation625 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14473step0 raw14473; decide +kernel
      have hl : raw14473step0Labels = raw14473Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14473 raw14473Labels permutation625 permutation5
    mixedMoment B raw14473step0 raw14473step0Labels = mixedMoment B raw14473step1 raw14473step1Labels := by
      have ha : raw14473step1 = raw14473step0 := by apply Matrix.ext; unfold raw14473step1 raw14473step0; decide +kernel
      have hl : raw14473step0Labels = labelEmbedding8 ∘ raw14473step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14473step0 raw14473step0Labels raw14473step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw14474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14474 raw14474Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw14474 raw14474Labels = mixedMoment B raw14474step0 raw14474step0Labels := by
      have ha : raw14474step0 = (fun i j => raw14474 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14474step0 raw14474; decide +kernel
      have hl : raw14474step0Labels = raw14474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14474 raw14474Labels permutation159 permutation2
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw14475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14475 raw14475Labels = mixedMoment B node5138 node5138Labels := by
  calc
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw14476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14476 raw14476Labels = mixedMoment B node5381 node5381Labels := by
  calc
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw14477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14477 raw14477Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw14477 raw14477Labels = mixedMoment B raw14477step0 raw14477step0Labels := by
      have ha : raw14477step0 = (fun i j => raw14477 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14477step0 raw14477; decide +kernel
      have hl : raw14477step0Labels = raw14477Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14477 raw14477Labels permutation176 permutation2
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw14478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14478 raw14478Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw14478 raw14478Labels = mixedMoment B raw14478step0 raw14478step0Labels := by
      have ha : raw14478step0 = (fun i j => raw14478 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14478step0 raw14478; decide +kernel
      have hl : raw14478step0Labels = raw14478Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14478 raw14478Labels permutation154 permutation2
    _ = mixedMoment B node5426 node5426Labels := by rfl

def raw14479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14479step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14479step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14479step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14479 raw14479Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw14479 raw14479Labels = mixedMoment B raw14479step0 raw14479step0Labels := by
      have ha : raw14479step0 = (fun i j => raw14479 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14479step0 raw14479; decide +kernel
      have hl : raw14479step0Labels = raw14479Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14479 raw14479Labels permutation180 permutation7
    mixedMoment B raw14479step0 raw14479step0Labels = mixedMoment B raw14479step1 raw14479step1Labels := by
      have ha : raw14479step1 = -raw14479step0 := by apply Matrix.ext; change ∀ i j, raw14479step1 i j = -(raw14479step0 i j); unfold raw14479step1 raw14479step0; decide +kernel
      have hl : raw14479step1Labels = raw14479step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14479step1 raw14479step1Labels = mixedMoment B raw14479step2 raw14479step2Labels := by
      have ha : raw14479step2 = raw14479step1 := by apply Matrix.ext; unfold raw14479step2 raw14479step1; decide +kernel
      have hl : raw14479step1Labels = labelEmbedding10 ∘ raw14479step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14479step1 raw14479step1Labels raw14479step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw14480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14480 raw14480Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw14480 raw14480Labels = mixedMoment B raw14480step0 raw14480step0Labels := by
      have ha : raw14480step0 = (fun i j => raw14480 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14480step0 raw14480; decide +kernel
      have hl : raw14480step0Labels = raw14480Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14480 raw14480Labels permutation153 permutation2
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw14481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14481 raw14481Labels = mixedMoment B node5376 node5376Labels := by
  calc
    mixedMoment B raw14481 raw14481Labels = mixedMoment B raw14481step0 raw14481step0Labels := by
      have ha : raw14481step0 = (fun i j => raw14481 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14481step0 raw14481; decide +kernel
      have hl : raw14481step0Labels = raw14481Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14481 raw14481Labels permutation153 permutation2
    _ = mixedMoment B node5376 node5376Labels := by rfl

def raw14482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14482 raw14482Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw14482 raw14482Labels = mixedMoment B raw14482step0 raw14482step0Labels := by
      have ha : raw14482step0 = (fun i j => raw14482 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14482step0 raw14482; decide +kernel
      have hl : raw14482step0Labels = raw14482Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14482 raw14482Labels permutation587 permutation2
    mixedMoment B raw14482step0 raw14482step0Labels = mixedMoment B raw14482step1 raw14482step1Labels := by
      have ha : raw14482step1 = -raw14482step0 := by apply Matrix.ext; change ∀ i j, raw14482step1 i j = -(raw14482step0 i j); unfold raw14482step1 raw14482step0; decide +kernel
      have hl : raw14482step1Labels = raw14482step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw14483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14483step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14483step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14483step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14483 raw14483Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw14483 raw14483Labels = mixedMoment B raw14483step0 raw14483step0Labels := by
      have ha : raw14483step0 = (fun i j => raw14483 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14483step0 raw14483; decide +kernel
      have hl : raw14483step0Labels = raw14483Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14483 raw14483Labels permutation680 permutation3
    mixedMoment B raw14483step0 raw14483step0Labels = mixedMoment B raw14483step1 raw14483step1Labels := by
      have ha : raw14483step1 = -raw14483step0 := by apply Matrix.ext; change ∀ i j, raw14483step1 i j = -(raw14483step0 i j); unfold raw14483step1 raw14483step0; decide +kernel
      have hl : raw14483step1Labels = raw14483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14483step1 raw14483step1Labels = mixedMoment B raw14483step2 raw14483step2Labels := by
      have ha : raw14483step2 = raw14483step1 := by apply Matrix.ext; unfold raw14483step2 raw14483step1; decide +kernel
      have hl : raw14483step1Labels = labelEmbedding6 ∘ raw14483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14483step1 raw14483step1Labels raw14483step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw14484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw14484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14484 raw14484Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw14484 raw14484Labels = mixedMoment B raw14484step0 raw14484step0Labels := by
      have ha : raw14484step0 = (fun i j => raw14484 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14484step0 raw14484; decide +kernel
      have hl : raw14484step0Labels = raw14484Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14484 raw14484Labels permutation153 permutation2
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw14485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14485step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14485step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14485 raw14485Labels = mixedMoment B node4824 node4824Labels := by
  calc
    mixedMoment B raw14485 raw14485Labels = mixedMoment B raw14485step0 raw14485step0Labels := by
      have ha : raw14485step0 = (fun i j => raw14485 (permutation646 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14485step0 raw14485; decide +kernel
      have hl : raw14485step0Labels = raw14485Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14485 raw14485Labels permutation646 permutation5
    mixedMoment B raw14485step0 raw14485step0Labels = mixedMoment B raw14485step1 raw14485step1Labels := by
      have ha : raw14485step1 = raw14485step0 := by apply Matrix.ext; unfold raw14485step1 raw14485step0; decide +kernel
      have hl : raw14485step0Labels = labelEmbedding8 ∘ raw14485step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14485step0 raw14485step0Labels raw14485step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4824 node4824Labels := by rfl

def raw14486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14486step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14486 raw14486Labels = mixedMoment B node4812 node4812Labels := by
  calc
    mixedMoment B raw14486 raw14486Labels = mixedMoment B raw14486step0 raw14486step0Labels := by
      have ha : raw14486step0 = (fun i j => raw14486 (permutation628 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14486step0 raw14486; decide +kernel
      have hl : raw14486step0Labels = raw14486Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14486 raw14486Labels permutation628 permutation5
    mixedMoment B raw14486step0 raw14486step0Labels = mixedMoment B raw14486step1 raw14486step1Labels := by
      have ha : raw14486step1 = raw14486step0 := by apply Matrix.ext; unfold raw14486step1 raw14486step0; decide +kernel
      have hl : raw14486step0Labels = labelEmbedding8 ∘ raw14486step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14486step0 raw14486step0Labels raw14486step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4812 node4812Labels := by rfl

def raw14487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14487step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14487step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14487step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14487step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14487step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14487 raw14487Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw14487 raw14487Labels = mixedMoment B raw14487step0 raw14487step0Labels := by
      have ha : raw14487step0 = (fun i j => raw14487 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14487step0 raw14487; decide +kernel
      have hl : raw14487step0Labels = raw14487Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14487 raw14487Labels permutation688 permutation3
    mixedMoment B raw14487step0 raw14487step0Labels = mixedMoment B raw14487step1 raw14487step1Labels := by
      have ha : raw14487step1 = -raw14487step0 := by apply Matrix.ext; change ∀ i j, raw14487step1 i j = -(raw14487step0 i j); unfold raw14487step1 raw14487step0; decide +kernel
      have hl : raw14487step1Labels = raw14487step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14487step1 raw14487step1Labels = mixedMoment B raw14487step2 raw14487step2Labels := by
      have ha : raw14487step2 = raw14487step1 := by apply Matrix.ext; unfold raw14487step2 raw14487step1; decide +kernel
      have hl : raw14487step1Labels = labelEmbedding6 ∘ raw14487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14487step1 raw14487step1Labels raw14487step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw14488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14488step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14488step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14488 raw14488Labels = mixedMoment B node4813 node4813Labels := by
  calc
    mixedMoment B raw14488 raw14488Labels = mixedMoment B raw14488step0 raw14488step0Labels := by
      have ha : raw14488step0 = (fun i j => raw14488 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14488step0 raw14488; decide +kernel
      have hl : raw14488step0Labels = raw14488Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14488 raw14488Labels permutation627 permutation5
    mixedMoment B raw14488step0 raw14488step0Labels = mixedMoment B raw14488step1 raw14488step1Labels := by
      have ha : raw14488step1 = raw14488step0 := by apply Matrix.ext; unfold raw14488step1 raw14488step0; decide +kernel
      have hl : raw14488step0Labels = labelEmbedding8 ∘ raw14488step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14488step0 raw14488step0Labels raw14488step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4813 node4813Labels := by rfl

def raw14489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw14489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14489step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14489step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14489 raw14489Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw14489 raw14489Labels = mixedMoment B raw14489step0 raw14489step0Labels := by
      have ha : raw14489step0 = (fun i j => raw14489 (permutation625 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14489step0 raw14489; decide +kernel
      have hl : raw14489step0Labels = raw14489Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14489 raw14489Labels permutation625 permutation5
    mixedMoment B raw14489step0 raw14489step0Labels = mixedMoment B raw14489step1 raw14489step1Labels := by
      have ha : raw14489step1 = raw14489step0 := by apply Matrix.ext; unfold raw14489step1 raw14489step0; decide +kernel
      have hl : raw14489step0Labels = labelEmbedding8 ∘ raw14489step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14489step0 raw14489step0Labels raw14489step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw14490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14490 raw14490Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw14490 raw14490Labels = mixedMoment B raw14490step0 raw14490step0Labels := by
      have ha : raw14490step0 = (fun i j => raw14490 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14490step0 raw14490; decide +kernel
      have hl : raw14490step0Labels = raw14490Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14490 raw14490Labels permutation271 permutation3
    _ = mixedMoment B node3870 node3870Labels := by rfl

def raw14491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14491 raw14491Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw14491 raw14491Labels = mixedMoment B raw14491step0 raw14491step0Labels := by
      have ha : raw14491step0 = (fun i j => raw14491 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14491step0 raw14491; decide +kernel
      have hl : raw14491step0Labels = raw14491Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14491 raw14491Labels permutation684 permutation3
    mixedMoment B raw14491step0 raw14491step0Labels = mixedMoment B raw14491step1 raw14491step1Labels := by
      have ha : raw14491step1 = -raw14491step0 := by apply Matrix.ext; change ∀ i j, raw14491step1 i j = -(raw14491step0 i j); unfold raw14491step1 raw14491step0; decide +kernel
      have hl : raw14491step1Labels = raw14491step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw14492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw14492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14492 raw14492Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw14492 raw14492Labels = mixedMoment B raw14492step0 raw14492step0Labels := by
      have ha : raw14492step0 = (fun i j => raw14492 (permutation677 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14492step0 raw14492; decide +kernel
      have hl : raw14492step0Labels = raw14492Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14492 raw14492Labels permutation677 permutation3
    mixedMoment B raw14492step0 raw14492step0Labels = mixedMoment B raw14492step1 raw14492step1Labels := by
      have ha : raw14492step1 = -raw14492step0 := by apply Matrix.ext; change ∀ i j, raw14492step1 i j = -(raw14492step0 i j); unfold raw14492step1 raw14492step0; decide +kernel
      have hl : raw14492step1Labels = raw14492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw14493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14493 raw14493Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw14493 raw14493Labels = mixedMoment B raw14493step0 raw14493step0Labels := by
      have ha : raw14493step0 = (fun i j => raw14493 (permutation559 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14493step0 raw14493; decide +kernel
      have hl : raw14493step0Labels = raw14493Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14493 raw14493Labels permutation559 permutation6
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw14494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14494 raw14494Labels = mixedMoment B node3971 node3971Labels := by
  calc
    mixedMoment B raw14494 raw14494Labels = mixedMoment B raw14494step0 raw14494step0Labels := by
      have ha : raw14494step0 = (fun i j => raw14494 (permutation559 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14494step0 raw14494; decide +kernel
      have hl : raw14494step0Labels = raw14494Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14494 raw14494Labels permutation559 permutation6
    _ = mixedMoment B node3971 node3971Labels := by rfl

def raw14495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14495 raw14495Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw14495 raw14495Labels = mixedMoment B raw14495step0 raw14495step0Labels := by
      have hz : ∀ j, raw14495 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14495step0 = (fun i j => raw14495 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14495step0 raw14495; decide +kernel
      have hl : raw14495step0Labels = raw14495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14495 raw14495Labels permutation265 hz
    mixedMoment B raw14495step0 raw14495step0Labels = mixedMoment B raw14495step1 raw14495step1Labels := by
      have ha : raw14495step1 = (fun i j => raw14495step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14495step1 raw14495step0; decide +kernel
      have hl : raw14495step1Labels = raw14495step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14495step0 raw14495step0Labels permutation38 permutation3
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw14496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw14496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14496 raw14496Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw14496 raw14496Labels = mixedMoment B raw14496step0 raw14496step0Labels := by
      have hz : ∀ j, raw14496 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14496step0 = (fun i j => raw14496 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14496step0 raw14496; decide +kernel
      have hl : raw14496step0Labels = raw14496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14496 raw14496Labels permutation265 hz
    mixedMoment B raw14496step0 raw14496step0Labels = mixedMoment B raw14496step1 raw14496step1Labels := by
      have ha : raw14496step1 = (fun i j => raw14496step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14496step1 raw14496step0; decide +kernel
      have hl : raw14496step1Labels = raw14496step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14496step0 raw14496step0Labels permutation151 permutation3
    mixedMoment B raw14496step1 raw14496step1Labels = mixedMoment B raw14496step2 raw14496step2Labels := by
      have ha : raw14496step2 = -raw14496step1 := by apply Matrix.ext; change ∀ i j, raw14496step2 i j = -(raw14496step1 i j); unfold raw14496step2 raw14496step1; decide +kernel
      have hl : raw14496step2Labels = raw14496step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw14497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14497 raw14497Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw14497 raw14497Labels = mixedMoment B raw14497step0 raw14497step0Labels := by
      have hz : ∀ j, raw14497 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14497step0 = (fun i j => raw14497 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14497step0 raw14497; decide +kernel
      have hl : raw14497step0Labels = raw14497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14497 raw14497Labels permutation265 hz
    mixedMoment B raw14497step0 raw14497step0Labels = mixedMoment B raw14497step1 raw14497step1Labels := by
      have ha : raw14497step1 = (fun i j => raw14497step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14497step1 raw14497step0; decide +kernel
      have hl : raw14497step1Labels = raw14497step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14497step0 raw14497step0Labels permutation149 permutation3
    mixedMoment B raw14497step1 raw14497step1Labels = mixedMoment B raw14497step2 raw14497step2Labels := by
      have ha : raw14497step2 = -raw14497step1 := by apply Matrix.ext; change ∀ i j, raw14497step2 i j = -(raw14497step1 i j); unfold raw14497step2 raw14497step1; decide +kernel
      have hl : raw14497step2Labels = raw14497step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw14498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14498 raw14498Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw14498 raw14498Labels = mixedMoment B raw14498step0 raw14498step0Labels := by
      have hz : ∀ j, raw14498 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14498step0 = (fun i j => raw14498 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14498step0 raw14498; decide +kernel
      have hl : raw14498step0Labels = raw14498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14498 raw14498Labels permutation265 hz
    mixedMoment B raw14498step0 raw14498step0Labels = mixedMoment B raw14498step1 raw14498step1Labels := by
      have ha : raw14498step1 = (fun i j => raw14498step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14498step1 raw14498step0; decide +kernel
      have hl : raw14498step1Labels = raw14498step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14498step0 raw14498step0Labels permutation121 permutation6
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw14499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14499 raw14499Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw14499 raw14499Labels = mixedMoment B raw14499step0 raw14499step0Labels := by
      have hz : ∀ j, raw14499 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14499step0 = (fun i j => raw14499 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14499step0 raw14499; decide +kernel
      have hl : raw14499step0Labels = raw14499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14499 raw14499Labels permutation265 hz
    mixedMoment B raw14499step0 raw14499step0Labels = mixedMoment B raw14499step1 raw14499step1Labels := by
      have ha : raw14499step1 = (fun i j => raw14499step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14499step1 raw14499step0; decide +kernel
      have hl : raw14499step1Labels = raw14499step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14499step0 raw14499step0Labels permutation121 permutation6
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw14500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14500 raw14500Labels = mixedMoment B node2922 node2922Labels := by
  calc
    mixedMoment B raw14500 raw14500Labels = mixedMoment B raw14500step0 raw14500step0Labels := by
      have ha : raw14500step0 = (fun i j => raw14500 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14500step0 raw14500; decide +kernel
      have hl : raw14500step0Labels = raw14500Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14500 raw14500Labels permutation160 permutation3
    _ = mixedMoment B node2922 node2922Labels := by rfl

def raw14501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14501 raw14501Labels = mixedMoment B node3718 node3718Labels := by
  calc
    mixedMoment B raw14501 raw14501Labels = mixedMoment B raw14501step0 raw14501step0Labels := by
      have ha : raw14501step0 = (fun i j => raw14501 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14501step0 raw14501; decide +kernel
      have hl : raw14501step0Labels = raw14501Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14501 raw14501Labels permutation273 permutation3
    _ = mixedMoment B node3718 node3718Labels := by rfl

def raw14502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14502 raw14502Labels = mixedMoment B node3752 node3752Labels := by
  calc
    mixedMoment B raw14502 raw14502Labels = mixedMoment B raw14502step0 raw14502step0Labels := by
      have ha : raw14502step0 = (fun i j => raw14502 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14502step0 raw14502; decide +kernel
      have hl : raw14502step0Labels = raw14502Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14502 raw14502Labels permutation644 permutation3
    mixedMoment B raw14502step0 raw14502step0Labels = mixedMoment B raw14502step1 raw14502step1Labels := by
      have ha : raw14502step1 = -raw14502step0 := by apply Matrix.ext; change ∀ i j, raw14502step1 i j = -(raw14502step0 i j); unfold raw14502step1 raw14502step0; decide +kernel
      have hl : raw14502step1Labels = raw14502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3752 node3752Labels := by rfl

def raw14503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14503 raw14503Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw14503 raw14503Labels = mixedMoment B raw14503step0 raw14503step0Labels := by
      have ha : raw14503step0 = (fun i j => raw14503 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14503step0 raw14503; decide +kernel
      have hl : raw14503step0Labels = raw14503Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14503 raw14503Labels permutation640 permutation3
    mixedMoment B raw14503step0 raw14503step0Labels = mixedMoment B raw14503step1 raw14503step1Labels := by
      have ha : raw14503step1 = -raw14503step0 := by apply Matrix.ext; change ∀ i j, raw14503step1 i j = -(raw14503step0 i j); unfold raw14503step1 raw14503step0; decide +kernel
      have hl : raw14503step1Labels = raw14503step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw14504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14504 raw14504Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw14504 raw14504Labels = mixedMoment B raw14504step0 raw14504step0Labels := by
      have ha : raw14504step0 = (fun i j => raw14504 (permutation559 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14504step0 raw14504; decide +kernel
      have hl : raw14504step0Labels = raw14504Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14504 raw14504Labels permutation559 permutation6
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw14505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14505 raw14505Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw14505 raw14505Labels = mixedMoment B raw14505step0 raw14505step0Labels := by
      have ha : raw14505step0 = (fun i j => raw14505 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14505step0 raw14505; decide +kernel
      have hl : raw14505step0Labels = raw14505Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14505 raw14505Labels permutation154 permutation3
    _ = mixedMoment B node2933 node2933Labels := by rfl

def raw14506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14506 raw14506Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw14506 raw14506Labels = mixedMoment B raw14506step0 raw14506step0Labels := by
      have ha : raw14506step0 = (fun i j => raw14506 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14506step0 raw14506; decide +kernel
      have hl : raw14506step0Labels = raw14506Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14506 raw14506Labels permutation267 permutation3
    _ = mixedMoment B node3723 node3723Labels := by rfl

def raw14507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14507 raw14507Labels = mixedMoment B node3830 node3830Labels := by
  calc
    mixedMoment B raw14507 raw14507Labels = mixedMoment B raw14507step0 raw14507step0Labels := by
      have ha : raw14507step0 = (fun i j => raw14507 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14507step0 raw14507; decide +kernel
      have hl : raw14507step0Labels = raw14507Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14507 raw14507Labels permutation664 permutation3
    mixedMoment B raw14507step0 raw14507step0Labels = mixedMoment B raw14507step1 raw14507step1Labels := by
      have ha : raw14507step1 = -raw14507step0 := by apply Matrix.ext; change ∀ i j, raw14507step1 i j = -(raw14507step0 i j); unfold raw14507step1 raw14507step0; decide +kernel
      have hl : raw14507step1Labels = raw14507step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3830 node3830Labels := by rfl

def raw14508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14508 raw14508Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw14508 raw14508Labels = mixedMoment B raw14508step0 raw14508step0Labels := by
      have ha : raw14508step0 = (fun i j => raw14508 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14508step0 raw14508; decide +kernel
      have hl : raw14508step0Labels = raw14508Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14508 raw14508Labels permutation658 permutation3
    mixedMoment B raw14508step0 raw14508step0Labels = mixedMoment B raw14508step1 raw14508step1Labels := by
      have ha : raw14508step1 = -raw14508step0 := by apply Matrix.ext; change ∀ i j, raw14508step1 i j = -(raw14508step0 i j); unfold raw14508step1 raw14508step0; decide +kernel
      have hl : raw14508step1Labels = raw14508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw14509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14509 raw14509Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw14509 raw14509Labels = mixedMoment B raw14509step0 raw14509step0Labels := by
      have ha : raw14509step0 = (fun i j => raw14509 (permutation559 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14509step0 raw14509; decide +kernel
      have hl : raw14509step0Labels = raw14509Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14509 raw14509Labels permutation559 permutation6
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw14510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14510 raw14510Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw14510 raw14510Labels = mixedMoment B raw14510step0 raw14510step0Labels := by
      have ha : raw14510step0 = (fun i j => raw14510 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14510step0 raw14510; decide +kernel
      have hl : raw14510step0Labels = raw14510Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14510 raw14510Labels permutation158 permutation3
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw14511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14511 raw14511Labels = mixedMoment B node3715 node3715Labels := by
  calc
    mixedMoment B raw14511 raw14511Labels = mixedMoment B raw14511step0 raw14511step0Labels := by
      have ha : raw14511step0 = (fun i j => raw14511 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14511step0 raw14511; decide +kernel
      have hl : raw14511step0Labels = raw14511Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14511 raw14511Labels permutation271 permutation3
    _ = mixedMoment B node3715 node3715Labels := by rfl

def raw14512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14512 raw14512Labels = mixedMoment B node3727 node3727Labels := by
  calc
    mixedMoment B raw14512 raw14512Labels = mixedMoment B raw14512step0 raw14512step0Labels := by
      have ha : raw14512step0 = (fun i j => raw14512 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14512step0 raw14512; decide +kernel
      have hl : raw14512step0Labels = raw14512Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14512 raw14512Labels permutation688 permutation3
    mixedMoment B raw14512step0 raw14512step0Labels = mixedMoment B raw14512step1 raw14512step1Labels := by
      have ha : raw14512step1 = -raw14512step0 := by apply Matrix.ext; change ∀ i j, raw14512step1 i j = -(raw14512step0 i j); unfold raw14512step1 raw14512step0; decide +kernel
      have hl : raw14512step1Labels = raw14512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3727 node3727Labels := by rfl

def raw14513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14513 raw14513Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw14513 raw14513Labels = mixedMoment B raw14513step0 raw14513step0Labels := by
      have ha : raw14513step0 = (fun i j => raw14513 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14513step0 raw14513; decide +kernel
      have hl : raw14513step0Labels = raw14513Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14513 raw14513Labels permutation680 permutation3
    mixedMoment B raw14513step0 raw14513step0Labels = mixedMoment B raw14513step1 raw14513step1Labels := by
      have ha : raw14513step1 = -raw14513step0 := by apply Matrix.ext; change ∀ i j, raw14513step1 i j = -(raw14513step0 i j); unfold raw14513step1 raw14513step0; decide +kernel
      have hl : raw14513step1Labels = raw14513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3722 node3722Labels := by rfl

def raw14514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw14514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14514 raw14514Labels = mixedMoment B node4032 node4032Labels := by
  calc
    mixedMoment B raw14514 raw14514Labels = mixedMoment B raw14514step0 raw14514step0Labels := by
      have ha : raw14514step0 = (fun i j => raw14514 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14514step0 raw14514; decide +kernel
      have hl : raw14514step0Labels = raw14514Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14514 raw14514Labels permutation159 permutation3
    _ = mixedMoment B node4032 node4032Labels := by rfl

def raw14515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw14515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw14515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14515 raw14515Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw14515 raw14515Labels = mixedMoment B raw14515step0 raw14515step0Labels := by
      have ha : raw14515step0 = (fun i j => raw14515 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14515step0 raw14515; decide +kernel
      have hl : raw14515step0Labels = raw14515Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14515 raw14515Labels permutation682 permutation3
    mixedMoment B raw14515step0 raw14515step0Labels = mixedMoment B raw14515step1 raw14515step1Labels := by
      have ha : raw14515step1 = -raw14515step0 := by apply Matrix.ext; change ∀ i j, raw14515step1 i j = -(raw14515step0 i j); unfold raw14515step1 raw14515step0; decide +kernel
      have hl : raw14515step1Labels = raw14515step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2071 node2071Labels := by rfl

def raw14516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw14516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14516 raw14516Labels = mixedMoment B node2072 node2072Labels := by
  calc
    mixedMoment B raw14516 raw14516Labels = mixedMoment B raw14516step0 raw14516step0Labels := by
      have ha : raw14516step0 = (fun i j => raw14516 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14516step0 raw14516; decide +kernel
      have hl : raw14516step0Labels = raw14516Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14516 raw14516Labels permutation681 permutation3
    mixedMoment B raw14516step0 raw14516step0Labels = mixedMoment B raw14516step1 raw14516step1Labels := by
      have ha : raw14516step1 = -raw14516step0 := by apply Matrix.ext; change ∀ i j, raw14516step1 i j = -(raw14516step0 i j); unfold raw14516step1 raw14516step0; decide +kernel
      have hl : raw14516step1Labels = raw14516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2072 node2072Labels := by rfl

def raw14517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14517 raw14517Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw14517 raw14517Labels = mixedMoment B raw14517step0 raw14517step0Labels := by
      have ha : raw14517step0 = (fun i j => raw14517 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14517step0 raw14517; decide +kernel
      have hl : raw14517step0Labels = raw14517Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14517 raw14517Labels permutation688 permutation3
    mixedMoment B raw14517step0 raw14517step0Labels = mixedMoment B raw14517step1 raw14517step1Labels := by
      have ha : raw14517step1 = -raw14517step0 := by apply Matrix.ext; change ∀ i j, raw14517step1 i j = -(raw14517step0 i j); unfold raw14517step1 raw14517step0; decide +kernel
      have hl : raw14517step1Labels = raw14517step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw14518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14518 raw14518Labels = mixedMoment B node2078 node2078Labels := by
  calc
    mixedMoment B raw14518 raw14518Labels = mixedMoment B raw14518step0 raw14518step0Labels := by
      have ha : raw14518step0 = (fun i j => raw14518 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14518step0 raw14518; decide +kernel
      have hl : raw14518step0Labels = raw14518Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14518 raw14518Labels permutation680 permutation3
    mixedMoment B raw14518step0 raw14518step0Labels = mixedMoment B raw14518step1 raw14518step1Labels := by
      have ha : raw14518step1 = -raw14518step0 := by apply Matrix.ext; change ∀ i j, raw14518step1 i j = -(raw14518step0 i j); unfold raw14518step1 raw14518step0; decide +kernel
      have hl : raw14518step1Labels = raw14518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2078 node2078Labels := by rfl

def raw14519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw14519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14519 raw14519Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw14519 raw14519Labels = mixedMoment B raw14519step0 raw14519step0Labels := by
      have ha : raw14519step0 = (fun i j => raw14519 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14519step0 raw14519; decide +kernel
      have hl : raw14519step0Labels = raw14519Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14519 raw14519Labels permutation640 permutation3
    mixedMoment B raw14519step0 raw14519step0Labels = mixedMoment B raw14519step1 raw14519step1Labels := by
      have ha : raw14519step1 = -raw14519step0 := by apply Matrix.ext; change ∀ i j, raw14519step1 i j = -(raw14519step0 i j); unfold raw14519step1 raw14519step0; decide +kernel
      have hl : raw14519step1Labels = raw14519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw14520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14520 raw14520Labels = mixedMoment B node3826 node3826Labels := by
  calc
    mixedMoment B raw14520 raw14520Labels = mixedMoment B raw14520step0 raw14520step0Labels := by
      have ha : raw14520step0 = (fun i j => raw14520 (permutation628 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14520step0 raw14520; decide +kernel
      have hl : raw14520step0Labels = raw14520Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14520 raw14520Labels permutation628 permutation5
    mixedMoment B raw14520step0 raw14520step0Labels = mixedMoment B raw14520step1 raw14520step1Labels := by
      have ha : raw14520step1 = raw14520step0 := by apply Matrix.ext; unfold raw14520step1 raw14520step0; decide +kernel
      have hl : raw14520step0Labels = labelEmbedding1 ∘ raw14520step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14520step0 raw14520step0Labels raw14520step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3826 node3826Labels := by rfl

def raw14521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14521step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14521 raw14521Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw14521 raw14521Labels = mixedMoment B raw14521step0 raw14521step0Labels := by
      have ha : raw14521step0 = (fun i j => raw14521 (permutation596 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14521step0 raw14521; decide +kernel
      have hl : raw14521step0Labels = raw14521Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14521 raw14521Labels permutation596 permutation5
    mixedMoment B raw14521step0 raw14521step0Labels = mixedMoment B raw14521step1 raw14521step1Labels := by
      have ha : raw14521step1 = raw14521step0 := by apply Matrix.ext; unfold raw14521step1 raw14521step0; decide +kernel
      have hl : raw14521step0Labels = labelEmbedding1 ∘ raw14521step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14521step0 raw14521step0Labels raw14521step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw14522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14522 raw14522Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw14522 raw14522Labels = mixedMoment B raw14522step0 raw14522step0Labels := by
      have ha : raw14522step0 = (fun i j => raw14522 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14522step0 raw14522; decide +kernel
      have hl : raw14522step0Labels = raw14522Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14522 raw14522Labels permutation627 permutation5
    mixedMoment B raw14522step0 raw14522step0Labels = mixedMoment B raw14522step1 raw14522step1Labels := by
      have ha : raw14522step1 = raw14522step0 := by apply Matrix.ext; unfold raw14522step1 raw14522step0; decide +kernel
      have hl : raw14522step0Labels = labelEmbedding1 ∘ raw14522step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14522step0 raw14522step0Labels raw14522step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3827 node3827Labels := by rfl

def raw14523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14523step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14523 raw14523Labels = mixedMoment B node3830 node3830Labels := by
  calc
    mixedMoment B raw14523 raw14523Labels = mixedMoment B raw14523step0 raw14523step0Labels := by
      have ha : raw14523step0 = (fun i j => raw14523 (permutation625 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14523step0 raw14523; decide +kernel
      have hl : raw14523step0Labels = raw14523Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14523 raw14523Labels permutation625 permutation5
    mixedMoment B raw14523step0 raw14523step0Labels = mixedMoment B raw14523step1 raw14523step1Labels := by
      have ha : raw14523step1 = raw14523step0 := by apply Matrix.ext; unfold raw14523step1 raw14523step0; decide +kernel
      have hl : raw14523step0Labels = labelEmbedding1 ∘ raw14523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14523step0 raw14523step0Labels raw14523step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3830 node3830Labels := by rfl

def raw14524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14524 raw14524Labels = mixedMoment B node3989 node3989Labels := by
  calc
    mixedMoment B raw14524 raw14524Labels = mixedMoment B raw14524step0 raw14524step0Labels := by
      have ha : raw14524step0 = (fun i j => raw14524 (permutation566 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14524step0 raw14524; decide +kernel
      have hl : raw14524step0Labels = raw14524Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14524 raw14524Labels permutation566 permutation7
    mixedMoment B raw14524step0 raw14524step0Labels = mixedMoment B raw14524step1 raw14524step1Labels := by
      have ha : raw14524step1 = raw14524step0 := by apply Matrix.ext; unfold raw14524step1 raw14524step0; decide +kernel
      have hl : raw14524step0Labels = labelEmbedding1 ∘ raw14524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14524step0 raw14524step0Labels raw14524step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3989 node3989Labels := by rfl

def raw14525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14525step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14525step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14525step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14525step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14525step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14525 raw14525Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw14525 raw14525Labels = mixedMoment B raw14525step0 raw14525step0Labels := by
      have hz : ∀ j, raw14525 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14525step0 = (fun i j => raw14525 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14525step0 raw14525; decide +kernel
      have hl : raw14525step0Labels = raw14525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14525 raw14525Labels permutation265 hz
    mixedMoment B raw14525step0 raw14525step0Labels = mixedMoment B raw14525step1 raw14525step1Labels := by
      have ha : raw14525step1 = (fun i j => raw14525step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14525step1 raw14525step0; decide +kernel
      have hl : raw14525step1Labels = raw14525step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14525step0 raw14525step0Labels permutation36 permutation7
    mixedMoment B raw14525step1 raw14525step1Labels = mixedMoment B raw14525step2 raw14525step2Labels := by
      have ha : raw14525step2 = -raw14525step1 := by apply Matrix.ext; change ∀ i j, raw14525step2 i j = -(raw14525step1 i j); unfold raw14525step2 raw14525step1; decide +kernel
      have hl : raw14525step2Labels = raw14525step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14525step2 raw14525step2Labels = mixedMoment B raw14525step3 raw14525step3Labels := by
      have ha : raw14525step3 = raw14525step2 := by apply Matrix.ext; unfold raw14525step3 raw14525step2; decide +kernel
      have hl : raw14525step2Labels = labelEmbedding1 ∘ raw14525step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14525step2 raw14525step2Labels raw14525step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw14526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14526step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14526step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14526 raw14526Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw14526 raw14526Labels = mixedMoment B raw14526step0 raw14526step0Labels := by
      have hz : ∀ j, raw14526 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14526step0 = (fun i j => raw14526 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14526step0 raw14526; decide +kernel
      have hl : raw14526step0Labels = raw14526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14526 raw14526Labels permutation265 hz
    mixedMoment B raw14526step0 raw14526step0Labels = mixedMoment B raw14526step1 raw14526step1Labels := by
      have ha : raw14526step1 = (fun i j => raw14526step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14526step1 raw14526step0; decide +kernel
      have hl : raw14526step1Labels = raw14526step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14526step0 raw14526step0Labels permutation36 permutation7
    mixedMoment B raw14526step1 raw14526step1Labels = mixedMoment B raw14526step2 raw14526step2Labels := by
      have ha : raw14526step2 = -raw14526step1 := by apply Matrix.ext; change ∀ i j, raw14526step2 i j = -(raw14526step1 i j); unfold raw14526step2 raw14526step1; decide +kernel
      have hl : raw14526step2Labels = raw14526step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14526step2 raw14526step2Labels = mixedMoment B raw14526step3 raw14526step3Labels := by
      have ha : raw14526step3 = raw14526step2 := by apply Matrix.ext; unfold raw14526step3 raw14526step2; decide +kernel
      have hl : raw14526step2Labels = labelEmbedding1 ∘ raw14526step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14526step2 raw14526step2Labels raw14526step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw14527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14527step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14527 raw14527Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw14527 raw14527Labels = mixedMoment B raw14527step0 raw14527step0Labels := by
      have hz : ∀ j, raw14527 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14527step0 = (fun i j => raw14527 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14527step0 raw14527; decide +kernel
      have hl : raw14527step0Labels = raw14527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14527 raw14527Labels permutation265 hz
    mixedMoment B raw14527step0 raw14527step0Labels = mixedMoment B raw14527step1 raw14527step1Labels := by
      have ha : raw14527step1 = (fun i j => raw14527step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14527step1 raw14527step0; decide +kernel
      have hl : raw14527step1Labels = raw14527step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14527step0 raw14527step0Labels permutation135 permutation5
    mixedMoment B raw14527step1 raw14527step1Labels = mixedMoment B raw14527step2 raw14527step2Labels := by
      have ha : raw14527step2 = raw14527step1 := by apply Matrix.ext; unfold raw14527step2 raw14527step1; decide +kernel
      have hl : raw14527step1Labels = labelEmbedding1 ∘ raw14527step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14527step1 raw14527step1Labels raw14527step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw14528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14528step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14528 raw14528Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw14528 raw14528Labels = mixedMoment B raw14528step0 raw14528step0Labels := by
      have hz : ∀ j, raw14528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14528step0 = (fun i j => raw14528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14528step0 raw14528; decide +kernel
      have hl : raw14528step0Labels = raw14528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14528 raw14528Labels permutation265 hz
    mixedMoment B raw14528step0 raw14528step0Labels = mixedMoment B raw14528step1 raw14528step1Labels := by
      have ha : raw14528step1 = (fun i j => raw14528step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14528step1 raw14528step0; decide +kernel
      have hl : raw14528step1Labels = raw14528step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14528step0 raw14528step0Labels permutation134 permutation5
    mixedMoment B raw14528step1 raw14528step1Labels = mixedMoment B raw14528step2 raw14528step2Labels := by
      have ha : raw14528step2 = raw14528step1 := by apply Matrix.ext; unfold raw14528step2 raw14528step1; decide +kernel
      have hl : raw14528step1Labels = labelEmbedding1 ∘ raw14528step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14528step1 raw14528step1Labels raw14528step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw14529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14529step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14529step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14529step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14529step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14529 raw14529Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw14529 raw14529Labels = mixedMoment B raw14529step0 raw14529step0Labels := by
      have hz : ∀ j, raw14529 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14529step0 = (fun i j => raw14529 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14529step0 raw14529; decide +kernel
      have hl : raw14529step0Labels = raw14529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14529 raw14529Labels permutation265 hz
    mixedMoment B raw14529step0 raw14529step0Labels = mixedMoment B raw14529step1 raw14529step1Labels := by
      have ha : raw14529step1 = (fun i j => raw14529step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14529step1 raw14529step0; decide +kernel
      have hl : raw14529step1Labels = raw14529step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14529step0 raw14529step0Labels permutation36 permutation7
    mixedMoment B raw14529step1 raw14529step1Labels = mixedMoment B raw14529step2 raw14529step2Labels := by
      have ha : raw14529step2 = -raw14529step1 := by apply Matrix.ext; change ∀ i j, raw14529step2 i j = -(raw14529step1 i j); unfold raw14529step2 raw14529step1; decide +kernel
      have hl : raw14529step2Labels = raw14529step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14529step2 raw14529step2Labels = mixedMoment B raw14529step3 raw14529step3Labels := by
      have ha : raw14529step3 = raw14529step2 := by apply Matrix.ext; unfold raw14529step3 raw14529step2; decide +kernel
      have hl : raw14529step2Labels = labelEmbedding1 ∘ raw14529step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14529step2 raw14529step2Labels raw14529step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw14530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14530step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14530step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14530 raw14530Labels = mixedMoment B node3560 node3560Labels := by
  calc
    mixedMoment B raw14530 raw14530Labels = mixedMoment B raw14530step0 raw14530step0Labels := by
      have ha : raw14530step0 = (fun i j => raw14530 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14530step0 raw14530; decide +kernel
      have hl : raw14530step0Labels = raw14530Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14530 raw14530Labels permutation180 permutation7
    mixedMoment B raw14530step0 raw14530step0Labels = mixedMoment B raw14530step1 raw14530step1Labels := by
      have ha : raw14530step1 = -raw14530step0 := by apply Matrix.ext; change ∀ i j, raw14530step1 i j = -(raw14530step0 i j); unfold raw14530step1 raw14530step0; decide +kernel
      have hl : raw14530step1Labels = raw14530step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14530step1 raw14530step1Labels = mixedMoment B raw14530step2 raw14530step2Labels := by
      have ha : raw14530step2 = raw14530step1 := by apply Matrix.ext; unfold raw14530step2 raw14530step1; decide +kernel
      have hl : raw14530step1Labels = labelEmbedding1 ∘ raw14530step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14530step1 raw14530step1Labels raw14530step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3560 node3560Labels := by rfl

def raw14531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14531step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14531 raw14531Labels = mixedMoment B node3695 node3695Labels := by
  calc
    mixedMoment B raw14531 raw14531Labels = mixedMoment B raw14531step0 raw14531step0Labels := by
      have ha : raw14531step0 = (fun i j => raw14531 (permutation628 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14531step0 raw14531; decide +kernel
      have hl : raw14531step0Labels = raw14531Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14531 raw14531Labels permutation628 permutation5
    mixedMoment B raw14531step0 raw14531step0Labels = mixedMoment B raw14531step1 raw14531step1Labels := by
      have ha : raw14531step1 = raw14531step0 := by apply Matrix.ext; unfold raw14531step1 raw14531step0; decide +kernel
      have hl : raw14531step0Labels = labelEmbedding1 ∘ raw14531step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14531step0 raw14531step0Labels raw14531step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3695 node3695Labels := by rfl

def raw14532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14532 raw14532Labels = mixedMoment B node3696 node3696Labels := by
  calc
    mixedMoment B raw14532 raw14532Labels = mixedMoment B raw14532step0 raw14532step0Labels := by
      have ha : raw14532step0 = (fun i j => raw14532 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14532step0 raw14532; decide +kernel
      have hl : raw14532step0Labels = raw14532Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14532 raw14532Labels permutation627 permutation5
    mixedMoment B raw14532step0 raw14532step0Labels = mixedMoment B raw14532step1 raw14532step1Labels := by
      have ha : raw14532step1 = raw14532step0 := by apply Matrix.ext; unfold raw14532step1 raw14532step0; decide +kernel
      have hl : raw14532step0Labels = labelEmbedding1 ∘ raw14532step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14532step0 raw14532step0Labels raw14532step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3696 node3696Labels := by rfl

def raw14533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14533Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14533step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14533 raw14533Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw14533 raw14533Labels = mixedMoment B raw14533step0 raw14533step0Labels := by
      have ha : raw14533step0 = (fun i j => raw14533 (permutation625 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14533step0 raw14533; decide +kernel
      have hl : raw14533step0Labels = raw14533Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14533 raw14533Labels permutation625 permutation5
    mixedMoment B raw14533step0 raw14533step0Labels = mixedMoment B raw14533step1 raw14533step1Labels := by
      have ha : raw14533step1 = raw14533step0 := by apply Matrix.ext; unfold raw14533step1 raw14533step0; decide +kernel
      have hl : raw14533step0Labels = labelEmbedding1 ∘ raw14533step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14533step0 raw14533step0Labels raw14533step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3698 node3698Labels := by rfl

def raw14534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14534step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14534 raw14534Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw14534 raw14534Labels = mixedMoment B raw14534step0 raw14534step0Labels := by
      have ha : raw14534step0 = (fun i j => raw14534 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14534step0 raw14534; decide +kernel
      have hl : raw14534step0Labels = raw14534Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14534 raw14534Labels permutation180 permutation7
    mixedMoment B raw14534step0 raw14534step0Labels = mixedMoment B raw14534step1 raw14534step1Labels := by
      have ha : raw14534step1 = -raw14534step0 := by apply Matrix.ext; change ∀ i j, raw14534step1 i j = -(raw14534step0 i j); unfold raw14534step1 raw14534step0; decide +kernel
      have hl : raw14534step1Labels = raw14534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14534step1 raw14534step1Labels = mixedMoment B raw14534step2 raw14534step2Labels := by
      have ha : raw14534step2 = raw14534step1 := by apply Matrix.ext; unfold raw14534step2 raw14534step1; decide +kernel
      have hl : raw14534step1Labels = labelEmbedding1 ∘ raw14534step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14534step1 raw14534step1Labels raw14534step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw14535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14535step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14535step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14535step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14535 raw14535Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw14535 raw14535Labels = mixedMoment B raw14535step0 raw14535step0Labels := by
      have ha : raw14535step0 = (fun i j => raw14535 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14535step0 raw14535; decide +kernel
      have hl : raw14535step0Labels = raw14535Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14535 raw14535Labels permutation180 permutation7
    mixedMoment B raw14535step0 raw14535step0Labels = mixedMoment B raw14535step1 raw14535step1Labels := by
      have ha : raw14535step1 = -raw14535step0 := by apply Matrix.ext; change ∀ i j, raw14535step1 i j = -(raw14535step0 i j); unfold raw14535step1 raw14535step0; decide +kernel
      have hl : raw14535step1Labels = raw14535step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14535step1 raw14535step1Labels = mixedMoment B raw14535step2 raw14535step2Labels := by
      have ha : raw14535step2 = raw14535step1 := by apply Matrix.ext; unfold raw14535step2 raw14535step1; decide +kernel
      have hl : raw14535step1Labels = labelEmbedding1 ∘ raw14535step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14535step1 raw14535step1Labels raw14535step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw14536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14536step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14536 raw14536Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw14536 raw14536Labels = mixedMoment B raw14536step0 raw14536step0Labels := by
      have ha : raw14536step0 = (fun i j => raw14536 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14536step0 raw14536; decide +kernel
      have hl : raw14536step0Labels = raw14536Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14536 raw14536Labels permutation180 permutation7
    mixedMoment B raw14536step0 raw14536step0Labels = mixedMoment B raw14536step1 raw14536step1Labels := by
      have ha : raw14536step1 = -raw14536step0 := by apply Matrix.ext; change ∀ i j, raw14536step1 i j = -(raw14536step0 i j); unfold raw14536step1 raw14536step0; decide +kernel
      have hl : raw14536step1Labels = raw14536step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14536step1 raw14536step1Labels = mixedMoment B raw14536step2 raw14536step2Labels := by
      have ha : raw14536step2 = raw14536step1 := by apply Matrix.ext; unfold raw14536step2 raw14536step1; decide +kernel
      have hl : raw14536step1Labels = labelEmbedding1 ∘ raw14536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14536step1 raw14536step1Labels raw14536step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw14537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14537step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14537step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14537 raw14537Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw14537 raw14537Labels = mixedMoment B raw14537step0 raw14537step0Labels := by
      have ha : raw14537step0 = (fun i j => raw14537 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14537step0 raw14537; decide +kernel
      have hl : raw14537step0Labels = raw14537Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14537 raw14537Labels permutation180 permutation7
    mixedMoment B raw14537step0 raw14537step0Labels = mixedMoment B raw14537step1 raw14537step1Labels := by
      have ha : raw14537step1 = -raw14537step0 := by apply Matrix.ext; change ∀ i j, raw14537step1 i j = -(raw14537step0 i j); unfold raw14537step1 raw14537step0; decide +kernel
      have hl : raw14537step1Labels = raw14537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14537step1 raw14537step1Labels = mixedMoment B raw14537step2 raw14537step2Labels := by
      have ha : raw14537step2 = raw14537step1 := by apply Matrix.ext; unfold raw14537step2 raw14537step1; decide +kernel
      have hl : raw14537step1Labels = labelEmbedding1 ∘ raw14537step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14537step1 raw14537step1Labels raw14537step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw14538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14538step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14538 raw14538Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw14538 raw14538Labels = mixedMoment B raw14538step0 raw14538step0Labels := by
      have ha : raw14538step0 = (fun i j => raw14538 (permutation635 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14538step0 raw14538; decide +kernel
      have hl : raw14538step0Labels = raw14538Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14538 raw14538Labels permutation635 permutation5
    mixedMoment B raw14538step0 raw14538step0Labels = mixedMoment B raw14538step1 raw14538step1Labels := by
      have ha : raw14538step1 = raw14538step0 := by apply Matrix.ext; unfold raw14538step1 raw14538step0; decide +kernel
      have hl : raw14538step0Labels = labelEmbedding1 ∘ raw14538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14538step0 raw14538step0Labels raw14538step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw14539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14539step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14539step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14539step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14539step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14539 raw14539Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw14539 raw14539Labels = mixedMoment B raw14539step0 raw14539step0Labels := by
      have ha : raw14539step0 = (fun i j => raw14539 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14539step0 raw14539; decide +kernel
      have hl : raw14539step0Labels = raw14539Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14539 raw14539Labels permutation180 permutation7
    mixedMoment B raw14539step0 raw14539step0Labels = mixedMoment B raw14539step1 raw14539step1Labels := by
      have ha : raw14539step1 = -raw14539step0 := by apply Matrix.ext; change ∀ i j, raw14539step1 i j = -(raw14539step0 i j); unfold raw14539step1 raw14539step0; decide +kernel
      have hl : raw14539step1Labels = raw14539step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14539step1 raw14539step1Labels = mixedMoment B raw14539step2 raw14539step2Labels := by
      have ha : raw14539step2 = raw14539step1 := by apply Matrix.ext; unfold raw14539step2 raw14539step1; decide +kernel
      have hl : raw14539step1Labels = labelEmbedding1 ∘ raw14539step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14539step1 raw14539step1Labels raw14539step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw14540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw14540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14540step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14540 raw14540Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw14540 raw14540Labels = mixedMoment B raw14540step0 raw14540step0Labels := by
      have ha : raw14540step0 = (fun i j => raw14540 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14540step0 raw14540; decide +kernel
      have hl : raw14540step0Labels = raw14540Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14540 raw14540Labels permutation180 permutation7
    mixedMoment B raw14540step0 raw14540step0Labels = mixedMoment B raw14540step1 raw14540step1Labels := by
      have ha : raw14540step1 = -raw14540step0 := by apply Matrix.ext; change ∀ i j, raw14540step1 i j = -(raw14540step0 i j); unfold raw14540step1 raw14540step0; decide +kernel
      have hl : raw14540step1Labels = raw14540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14540step1 raw14540step1Labels = mixedMoment B raw14540step2 raw14540step2Labels := by
      have ha : raw14540step2 = raw14540step1 := by apply Matrix.ext; unfold raw14540step2 raw14540step1; decide +kernel
      have hl : raw14540step1Labels = labelEmbedding1 ∘ raw14540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14540step1 raw14540step1Labels raw14540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw14541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14541step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14541 raw14541Labels = mixedMoment B node3833 node3833Labels := by
  calc
    mixedMoment B raw14541 raw14541Labels = mixedMoment B raw14541step0 raw14541step0Labels := by
      have ha : raw14541step0 = (fun i j => raw14541 (permutation642 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14541step0 raw14541; decide +kernel
      have hl : raw14541step0Labels = raw14541Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14541 raw14541Labels permutation642 permutation5
    mixedMoment B raw14541step0 raw14541step0Labels = mixedMoment B raw14541step1 raw14541step1Labels := by
      have ha : raw14541step1 = raw14541step0 := by apply Matrix.ext; unfold raw14541step1 raw14541step0; decide +kernel
      have hl : raw14541step0Labels = labelEmbedding1 ∘ raw14541step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14541step0 raw14541step0Labels raw14541step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3833 node3833Labels := by rfl

def raw14542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw14542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14542step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw14542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14542 raw14542Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw14542 raw14542Labels = mixedMoment B raw14542step0 raw14542step0Labels := by
      have ha : raw14542step0 = (fun i j => raw14542 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14542step0 raw14542; decide +kernel
      have hl : raw14542step0Labels = raw14542Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14542 raw14542Labels permutation180 permutation7
    mixedMoment B raw14542step0 raw14542step0Labels = mixedMoment B raw14542step1 raw14542step1Labels := by
      have ha : raw14542step1 = -raw14542step0 := by apply Matrix.ext; change ∀ i j, raw14542step1 i j = -(raw14542step0 i j); unfold raw14542step1 raw14542step0; decide +kernel
      have hl : raw14542step1Labels = raw14542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14542step1 raw14542step1Labels = mixedMoment B raw14542step2 raw14542step2Labels := by
      have ha : raw14542step2 = raw14542step1 := by apply Matrix.ext; unfold raw14542step2 raw14542step1; decide +kernel
      have hl : raw14542step1Labels = labelEmbedding1 ∘ raw14542step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14542step1 raw14542step1Labels raw14542step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw14543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14543step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14543 raw14543Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw14543 raw14543Labels = mixedMoment B raw14543step0 raw14543step0Labels := by
      have ha : raw14543step0 = (fun i j => raw14543 (permutation641 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14543step0 raw14543; decide +kernel
      have hl : raw14543step0Labels = raw14543Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14543 raw14543Labels permutation641 permutation5
    mixedMoment B raw14543step0 raw14543step0Labels = mixedMoment B raw14543step1 raw14543step1Labels := by
      have ha : raw14543step1 = raw14543step0 := by apply Matrix.ext; unfold raw14543step1 raw14543step0; decide +kernel
      have hl : raw14543step0Labels = labelEmbedding1 ∘ raw14543step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14543step0 raw14543step0Labels raw14543step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw14544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw14544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14544 raw14544Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw14544 raw14544Labels = mixedMoment B raw14544step0 raw14544step0Labels := by
      have ha : raw14544step0 = (fun i j => raw14544 (permutation566 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14544step0 raw14544; decide +kernel
      have hl : raw14544step0Labels = raw14544Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14544 raw14544Labels permutation566 permutation7
    mixedMoment B raw14544step0 raw14544step0Labels = mixedMoment B raw14544step1 raw14544step1Labels := by
      have ha : raw14544step1 = raw14544step0 := by apply Matrix.ext; unfold raw14544step1 raw14544step0; decide +kernel
      have hl : raw14544step0Labels = labelEmbedding1 ∘ raw14544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14544step0 raw14544step0Labels raw14544step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw14545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14545step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14545 raw14545Labels = mixedMoment B node2043 node2043Labels := by
  calc
    mixedMoment B raw14545 raw14545Labels = mixedMoment B raw14545step0 raw14545step0Labels := by
      have ha : raw14545step0 = (fun i j => raw14545 (permutation646 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14545step0 raw14545; decide +kernel
      have hl : raw14545step0Labels = raw14545Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14545 raw14545Labels permutation646 permutation5
    mixedMoment B raw14545step0 raw14545step0Labels = mixedMoment B raw14545step1 raw14545step1Labels := by
      have ha : raw14545step1 = raw14545step0 := by apply Matrix.ext; unfold raw14545step1 raw14545step0; decide +kernel
      have hl : raw14545step0Labels = labelEmbedding1 ∘ raw14545step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14545step0 raw14545step0Labels raw14545step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2043 node2043Labels := by rfl

def raw14546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14546step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14546 raw14546Labels = mixedMoment B node2030 node2030Labels := by
  calc
    mixedMoment B raw14546 raw14546Labels = mixedMoment B raw14546step0 raw14546step0Labels := by
      have ha : raw14546step0 = (fun i j => raw14546 (permutation628 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14546step0 raw14546; decide +kernel
      have hl : raw14546step0Labels = raw14546Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14546 raw14546Labels permutation628 permutation5
    mixedMoment B raw14546step0 raw14546step0Labels = mixedMoment B raw14546step1 raw14546step1Labels := by
      have ha : raw14546step1 = raw14546step0 := by apply Matrix.ext; unfold raw14546step1 raw14546step0; decide +kernel
      have hl : raw14546step0Labels = labelEmbedding1 ∘ raw14546step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14546step0 raw14546step0Labels raw14546step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2030 node2030Labels := by rfl

def raw14547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14547Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14547step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14547 raw14547Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw14547 raw14547Labels = mixedMoment B raw14547step0 raw14547step0Labels := by
      have ha : raw14547step0 = (fun i j => raw14547 (permutation628 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14547step0 raw14547; decide +kernel
      have hl : raw14547step0Labels = raw14547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14547 raw14547Labels permutation628 permutation5
    mixedMoment B raw14547step0 raw14547step0Labels = mixedMoment B raw14547step1 raw14547step1Labels := by
      have ha : raw14547step1 = raw14547step0 := by apply Matrix.ext; unfold raw14547step1 raw14547step0; decide +kernel
      have hl : raw14547step0Labels = labelEmbedding1 ∘ raw14547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14547step0 raw14547step0Labels raw14547step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw14548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14548 raw14548Labels = mixedMoment B node2031 node2031Labels := by
  calc
    mixedMoment B raw14548 raw14548Labels = mixedMoment B raw14548step0 raw14548step0Labels := by
      have ha : raw14548step0 = (fun i j => raw14548 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14548step0 raw14548; decide +kernel
      have hl : raw14548step0Labels = raw14548Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14548 raw14548Labels permutation627 permutation5
    mixedMoment B raw14548step0 raw14548step0Labels = mixedMoment B raw14548step1 raw14548step1Labels := by
      have ha : raw14548step1 = raw14548step0 := by apply Matrix.ext; unfold raw14548step1 raw14548step0; decide +kernel
      have hl : raw14548step0Labels = labelEmbedding1 ∘ raw14548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14548step0 raw14548step0Labels raw14548step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2031 node2031Labels := by rfl

def raw14549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw14549Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14549step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14549 raw14549Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw14549 raw14549Labels = mixedMoment B raw14549step0 raw14549step0Labels := by
      have ha : raw14549step0 = (fun i j => raw14549 (permutation625 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14549step0 raw14549; decide +kernel
      have hl : raw14549step0Labels = raw14549Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14549 raw14549Labels permutation625 permutation5
    mixedMoment B raw14549step0 raw14549step0Labels = mixedMoment B raw14549step1 raw14549step1Labels := by
      have ha : raw14549step1 = raw14549step0 := by apply Matrix.ext; unfold raw14549step1 raw14549step0; decide +kernel
      have hl : raw14549step0Labels = labelEmbedding1 ∘ raw14549step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14549step0 raw14549step0Labels raw14549step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2034 node2034Labels := by rfl

def raw14550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14550 raw14550Labels = mixedMoment B node3839 node3839Labels := by
  calc
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw14551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14551 raw14551Labels = mixedMoment B node4022 node4022Labels := by
  calc
    mixedMoment B raw14551 raw14551Labels = mixedMoment B raw14551step0 raw14551step0Labels := by
      have ha : raw14551step0 = (fun i j => raw14551 (permutation595 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14551step0 raw14551; decide +kernel
      have hl : raw14551step0Labels = raw14551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14551 raw14551Labels permutation595 permutation4
    _ = mixedMoment B node4022 node4022Labels := by rfl

def raw14552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw14552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14552 raw14552Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw14552 raw14552Labels = mixedMoment B raw14552step0 raw14552step0Labels := by
      have ha : raw14552step0 = (fun i j => raw14552 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14552step0 raw14552; decide +kernel
      have hl : raw14552step0Labels = raw14552Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14552 raw14552Labels permutation686 permutation2
    mixedMoment B raw14552step0 raw14552step0Labels = mixedMoment B raw14552step1 raw14552step1Labels := by
      have ha : raw14552step1 = -raw14552step0 := by apply Matrix.ext; change ∀ i j, raw14552step1 i j = -(raw14552step0 i j); unfold raw14552step1 raw14552step0; decide +kernel
      have hl : raw14552step1Labels = raw14552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw14553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14553 raw14553Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw14553 raw14553Labels = mixedMoment B raw14553step0 raw14553step0Labels := by
      have ha : raw14553step0 = (fun i j => raw14553 (permutation491 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14553step0 raw14553; decide +kernel
      have hl : raw14553step0Labels = raw14553Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14553 raw14553Labels permutation491 permutation4
    mixedMoment B raw14553step0 raw14553step0Labels = mixedMoment B raw14553step1 raw14553step1Labels := by
      have ha : raw14553step1 = -raw14553step0 := by apply Matrix.ext; change ∀ i j, raw14553step1 i j = -(raw14553step0 i j); unfold raw14553step1 raw14553step0; decide +kernel
      have hl : raw14553step1Labels = raw14553step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw14554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14554 raw14554Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw14554 raw14554Labels = mixedMoment B raw14554step0 raw14554step0Labels := by
      have ha : raw14554step0 = (fun i j => raw14554 (permutation556 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14554step0 raw14554; decide +kernel
      have hl : raw14554step0Labels = raw14554Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14554 raw14554Labels permutation556 permutation4
    mixedMoment B raw14554step0 raw14554step0Labels = mixedMoment B raw14554step1 raw14554step1Labels := by
      have ha : raw14554step1 = -raw14554step0 := by apply Matrix.ext; change ∀ i j, raw14554step1 i j = -(raw14554step0 i j); unfold raw14554step1 raw14554step0; decide +kernel
      have hl : raw14554step1Labels = raw14554step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw14555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14555 raw14555Labels = mixedMoment B node4044 node4044Labels := by
  calc
    mixedMoment B raw14555 raw14555Labels = mixedMoment B raw14555step0 raw14555step0Labels := by
      have ha : raw14555step0 = (fun i j => raw14555 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14555step0 raw14555; decide +kernel
      have hl : raw14555step0Labels = raw14555Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14555 raw14555Labels permutation194 permutation4
    _ = mixedMoment B node4044 node4044Labels := by rfl

def raw14556 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]
def raw14556Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14556step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw14556step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14556step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw14556step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14556 raw14556Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw14556 raw14556Labels = mixedMoment B raw14556step0 raw14556step0Labels := by
      have hz : ∀ j, raw14556 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14556step0 = (fun i j => raw14556 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14556step0 raw14556; decide +kernel
      have hl : raw14556step0Labels = raw14556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14556 raw14556Labels permutation590 hz
    mixedMoment B raw14556step0 raw14556step0Labels = mixedMoment B raw14556step1 raw14556step1Labels := by
      have hz : ∀ j, raw14556step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14556step1 = (fun i j => raw14556step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14556step1 raw14556step0; decide +kernel
      have hl : raw14556step1Labels = raw14556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14556step0 raw14556step0Labels permutation56 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw14557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14557 raw14557Labels = mixedMoment B node3725 node3725Labels := by
  calc
    mixedMoment B raw14557 raw14557Labels = mixedMoment B raw14557step0 raw14557step0Labels := by
      have ha : raw14557step0 = (fun i j => raw14557 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14557step0 raw14557; decide +kernel
      have hl : raw14557step0Labels = raw14557Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14557 raw14557Labels permutation158 permutation2
    _ = mixedMoment B node3725 node3725Labels := by rfl

def raw14558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14558 raw14558Labels = mixedMoment B node3722 node3722Labels := by
  calc
    _ = mixedMoment B node3722 node3722Labels := by rfl

def raw14559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14559 raw14559Labels = mixedMoment B node3715 node3715Labels := by
  calc
    mixedMoment B raw14559 raw14559Labels = mixedMoment B raw14559step0 raw14559step0Labels := by
      have ha : raw14559step0 = (fun i j => raw14559 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14559step0 raw14559; decide +kernel
      have hl : raw14559step0Labels = raw14559Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14559 raw14559Labels permutation153 permutation2
    _ = mixedMoment B node3715 node3715Labels := by rfl

def raw14560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw14560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14560 raw14560Labels = mixedMoment B node3168 node3168Labels := by
  calc
    mixedMoment B raw14560 raw14560Labels = mixedMoment B raw14560step0 raw14560step0Labels := by
      have ha : raw14560step0 = (fun i j => raw14560 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14560step0 raw14560; decide +kernel
      have hl : raw14560step0Labels = raw14560Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14560 raw14560Labels permutation688 permutation2
    mixedMoment B raw14560step0 raw14560step0Labels = mixedMoment B raw14560step1 raw14560step1Labels := by
      have ha : raw14560step1 = -raw14560step0 := by apply Matrix.ext; change ∀ i j, raw14560step1 i j = -(raw14560step0 i j); unfold raw14560step1 raw14560step0; decide +kernel
      have hl : raw14560step1Labels = raw14560step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3168 node3168Labels := by rfl

def raw14561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14561 raw14561Labels = mixedMoment B node2568 node2568Labels := by
  calc
    mixedMoment B raw14561 raw14561Labels = mixedMoment B raw14561step0 raw14561step0Labels := by
      have ha : raw14561step0 = (fun i j => raw14561 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14561step0 raw14561; decide +kernel
      have hl : raw14561step0Labels = raw14561Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14561 raw14561Labels permutation158 permutation2
    _ = mixedMoment B node2568 node2568Labels := by rfl

def raw14562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14562 raw14562Labels = mixedMoment B node3828 node3828Labels := by
  calc
    mixedMoment B raw14562 raw14562Labels = mixedMoment B raw14562step0 raw14562step0Labels := by
      have ha : raw14562step0 = (fun i j => raw14562 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14562step0 raw14562; decide +kernel
      have hl : raw14562step0Labels = raw14562Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14562 raw14562Labels permutation158 permutation2
    _ = mixedMoment B node3828 node3828Labels := by rfl

def raw14563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14563 raw14563Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw14563 raw14563Labels = mixedMoment B raw14563step0 raw14563step0Labels := by
      have ha : raw14563step0 = (fun i j => raw14563 (permutation555 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14563step0 raw14563; decide +kernel
      have hl : raw14563step0Labels = raw14563Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14563 raw14563Labels permutation555 permutation4
    mixedMoment B raw14563step0 raw14563step0Labels = mixedMoment B raw14563step1 raw14563step1Labels := by
      have ha : raw14563step1 = -raw14563step0 := by apply Matrix.ext; change ∀ i j, raw14563step1 i j = -(raw14563step0 i j); unfold raw14563step1 raw14563step0; decide +kernel
      have hl : raw14563step1Labels = raw14563step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3780 node3780Labels := by rfl

def raw14564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14564 raw14564Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw14564 raw14564Labels = mixedMoment B raw14564step0 raw14564step0Labels := by
      have ha : raw14564step0 = (fun i j => raw14564 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14564step0 raw14564; decide +kernel
      have hl : raw14564step0Labels = raw14564Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14564 raw14564Labels permutation159 permutation2
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw14565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14565 raw14565Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw14565 raw14565Labels = mixedMoment B raw14565step0 raw14565step0Labels := by
      have hz : ∀ j, raw14565 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14565step0 = (fun i j => raw14565 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14565step0 raw14565; decide +kernel
      have hl : raw14565step0Labels = raw14565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14565 raw14565Labels permutation265 hz
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw14566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14566 raw14566Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw14566 raw14566Labels = mixedMoment B raw14566step0 raw14566step0Labels := by
      have ha : raw14566step0 = (fun i j => raw14566 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14566step0 raw14566; decide +kernel
      have hl : raw14566step0Labels = raw14566Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14566 raw14566Labels permutation176 permutation2
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw14567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14567 raw14567Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw14567 raw14567Labels = mixedMoment B raw14567step0 raw14567step0Labels := by
      have ha : raw14567step0 = (fun i j => raw14567 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14567step0 raw14567; decide +kernel
      have hl : raw14567step0Labels = raw14567Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14567 raw14567Labels permutation587 permutation2
    mixedMoment B raw14567step0 raw14567step0Labels = mixedMoment B raw14567step1 raw14567step1Labels := by
      have ha : raw14567step1 = -raw14567step0 := by apply Matrix.ext; change ∀ i j, raw14567step1 i j = -(raw14567step0 i j); unfold raw14567step1 raw14567step0; decide +kernel
      have hl : raw14567step1Labels = raw14567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw14568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14568 raw14568Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw14568 raw14568Labels = mixedMoment B raw14568step0 raw14568step0Labels := by
      have ha : raw14568step0 = (fun i j => raw14568 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14568step0 raw14568; decide +kernel
      have hl : raw14568step0Labels = raw14568Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14568 raw14568Labels permutation686 permutation2
    mixedMoment B raw14568step0 raw14568step0Labels = mixedMoment B raw14568step1 raw14568step1Labels := by
      have ha : raw14568step1 = -raw14568step0 := by apply Matrix.ext; change ∀ i j, raw14568step1 i j = -(raw14568step0 i j); unfold raw14568step1 raw14568step0; decide +kernel
      have hl : raw14568step1Labels = raw14568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw14569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14569 raw14569Labels = mixedMoment B node2557 node2557Labels := by
  calc
    _ = mixedMoment B node2557 node2557Labels := by rfl

def raw14570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14570 raw14570Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw14570 raw14570Labels = mixedMoment B raw14570step0 raw14570step0Labels := by
      have ha : raw14570step0 = (fun i j => raw14570 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14570step0 raw14570; decide +kernel
      have hl : raw14570step0Labels = raw14570Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14570 raw14570Labels permutation154 permutation2
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw14571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw14571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14571 raw14571Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw14571 raw14571Labels = mixedMoment B raw14571step0 raw14571step0Labels := by
      have ha : raw14571step0 = (fun i j => raw14571 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14571step0 raw14571; decide +kernel
      have hl : raw14571step0Labels = raw14571Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14571 raw14571Labels permutation156 permutation2
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw14572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14572 raw14572Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw14572 raw14572Labels = mixedMoment B raw14572step0 raw14572step0Labels := by
      have hz : ∀ j, raw14572 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14572step0 = (fun i j => raw14572 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14572step0 raw14572; decide +kernel
      have hl : raw14572step0Labels = raw14572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14572 raw14572Labels permutation265 hz
    mixedMoment B raw14572step0 raw14572step0Labels = mixedMoment B raw14572step1 raw14572step1Labels := by
      have ha : raw14572step1 = (fun i j => raw14572step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14572step1 raw14572step0; decide +kernel
      have hl : raw14572step1Labels = raw14572step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14572step0 raw14572step0Labels permutation38 permutation2
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw14573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14573 raw14573Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw14573 raw14573Labels = mixedMoment B raw14573step0 raw14573step0Labels := by
      have ha : raw14573step0 = (fun i j => raw14573 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14573step0 raw14573; decide +kernel
      have hl : raw14573step0Labels = raw14573Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14573 raw14573Labels permutation584 permutation2
    mixedMoment B raw14573step0 raw14573step0Labels = mixedMoment B raw14573step1 raw14573step1Labels := by
      have ha : raw14573step1 = -raw14573step0 := by apply Matrix.ext; change ∀ i j, raw14573step1 i j = -(raw14573step0 i j); unfold raw14573step1 raw14573step0; decide +kernel
      have hl : raw14573step1Labels = raw14573step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3723 node3723Labels := by rfl

def raw14574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14574 raw14574Labels = mixedMoment B node3175 node3175Labels := by
  calc
    mixedMoment B raw14574 raw14574Labels = mixedMoment B raw14574step0 raw14574step0Labels := by
      have ha : raw14574step0 = (fun i j => raw14574 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14574step0 raw14574; decide +kernel
      have hl : raw14574step0Labels = raw14574Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14574 raw14574Labels permutation682 permutation2
    mixedMoment B raw14574step0 raw14574step0Labels = mixedMoment B raw14574step1 raw14574step1Labels := by
      have ha : raw14574step1 = -raw14574step0 := by apply Matrix.ext; change ∀ i j, raw14574step1 i j = -(raw14574step0 i j); unfold raw14574step1 raw14574step0; decide +kernel
      have hl : raw14574step1Labels = raw14574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3175 node3175Labels := by rfl

def raw14575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw14575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14575 raw14575Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw14575 raw14575Labels = mixedMoment B raw14575step0 raw14575step0Labels := by
      have ha : raw14575step0 = (fun i j => raw14575 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14575step0 raw14575; decide +kernel
      have hl : raw14575step0Labels = raw14575Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14575 raw14575Labels permutation153 permutation2
    _ = mixedMoment B node2545 node2545Labels := by rfl

def raw14576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw14576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14576 raw14576Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw14576 raw14576Labels = mixedMoment B raw14576step0 raw14576step0Labels := by
      have ha : raw14576step0 = (fun i j => raw14576 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14576step0 raw14576; decide +kernel
      have hl : raw14576step0Labels = raw14576Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14576 raw14576Labels permutation153 permutation2
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw14577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14577 raw14577Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw14577 raw14577Labels = mixedMoment B raw14577step0 raw14577step0Labels := by
      have hz : ∀ j, raw14577 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14577step0 = (fun i j => raw14577 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14577step0 raw14577; decide +kernel
      have hl : raw14577step0Labels = raw14577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14577 raw14577Labels permutation265 hz
    mixedMoment B raw14577step0 raw14577step0Labels = mixedMoment B raw14577step1 raw14577step1Labels := by
      have ha : raw14577step1 = (fun i j => raw14577step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14577step1 raw14577step0; decide +kernel
      have hl : raw14577step1Labels = raw14577step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14577step0 raw14577step0Labels permutation116 permutation4
    mixedMoment B raw14577step1 raw14577step1Labels = mixedMoment B raw14577step2 raw14577step2Labels := by
      have ha : raw14577step2 = -raw14577step1 := by apply Matrix.ext; change ∀ i j, raw14577step2 i j = -(raw14577step1 i j); unfold raw14577step2 raw14577step1; decide +kernel
      have hl : raw14577step2Labels = raw14577step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw14578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw14578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14578 raw14578Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw14578 raw14578Labels = mixedMoment B raw14578step0 raw14578step0Labels := by
      have ha : raw14578step0 = (fun i j => raw14578 (permutation623 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14578step0 raw14578; decide +kernel
      have hl : raw14578step0Labels = raw14578Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14578 raw14578Labels permutation623 permutation4
    _ = mixedMoment B node3196 node3196Labels := by rfl

def raw14579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw14579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14579 raw14579Labels = mixedMoment B node2544 node2544Labels := by
  calc
    _ = mixedMoment B node2544 node2544Labels := by rfl

def raw14580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14580step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14580 raw14580Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw14580 raw14580Labels = mixedMoment B raw14580step0 raw14580step0Labels := by
      have ha : raw14580step0 = (fun i j => raw14580 (permutation628 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14580step0 raw14580; decide +kernel
      have hl : raw14580step0Labels = raw14580Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14580 raw14580Labels permutation628 permutation7
    mixedMoment B raw14580step0 raw14580step0Labels = mixedMoment B raw14580step1 raw14580step1Labels := by
      have ha : raw14580step1 = raw14580step0 := by apply Matrix.ext; unfold raw14580step1 raw14580step0; decide +kernel
      have hl : raw14580step0Labels = labelEmbedding10 ∘ raw14580step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14580step0 raw14580step0Labels raw14580step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw14581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14581 raw14581Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw14581 raw14581Labels = mixedMoment B raw14581step0 raw14581step0Labels := by
      have ha : raw14581step0 = (fun i j => raw14581 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14581step0 raw14581; decide +kernel
      have hl : raw14581step0Labels = raw14581Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14581 raw14581Labels permutation687 permutation2
    mixedMoment B raw14581step0 raw14581step0Labels = mixedMoment B raw14581step1 raw14581step1Labels := by
      have ha : raw14581step1 = -raw14581step0 := by apply Matrix.ext; change ∀ i j, raw14581step1 i j = -(raw14581step0 i j); unfold raw14581step1 raw14581step0; decide +kernel
      have hl : raw14581step1Labels = raw14581step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw14582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14582step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14582 raw14582Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw14582 raw14582Labels = mixedMoment B raw14582step0 raw14582step0Labels := by
      have ha : raw14582step0 = (fun i j => raw14582 (permutation627 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14582step0 raw14582; decide +kernel
      have hl : raw14582step0Labels = raw14582Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14582 raw14582Labels permutation627 permutation7
    mixedMoment B raw14582step0 raw14582step0Labels = mixedMoment B raw14582step1 raw14582step1Labels := by
      have ha : raw14582step1 = raw14582step0 := by apply Matrix.ext; unfold raw14582step1 raw14582step0; decide +kernel
      have hl : raw14582step0Labels = labelEmbedding10 ∘ raw14582step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14582step0 raw14582step0Labels raw14582step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw14583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14583step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14583 raw14583Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw14583 raw14583Labels = mixedMoment B raw14583step0 raw14583step0Labels := by
      have ha : raw14583step0 = (fun i j => raw14583 (permutation626 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14583step0 raw14583; decide +kernel
      have hl : raw14583step0Labels = raw14583Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14583 raw14583Labels permutation626 permutation7
    mixedMoment B raw14583step0 raw14583step0Labels = mixedMoment B raw14583step1 raw14583step1Labels := by
      have ha : raw14583step1 = raw14583step0 := by apply Matrix.ext; unfold raw14583step1 raw14583step0; decide +kernel
      have hl : raw14583step0Labels = labelEmbedding10 ∘ raw14583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14583step0 raw14583step0Labels raw14583step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw14584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14584step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14584 raw14584Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw14584 raw14584Labels = mixedMoment B raw14584step0 raw14584step0Labels := by
      have ha : raw14584step0 = (fun i j => raw14584 (permutation554 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14584step0 raw14584; decide +kernel
      have hl : raw14584step0Labels = raw14584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14584 raw14584Labels permutation554 permutation4
    mixedMoment B raw14584step0 raw14584step0Labels = mixedMoment B raw14584step1 raw14584step1Labels := by
      have ha : raw14584step1 = raw14584step0 := by apply Matrix.ext; unfold raw14584step1 raw14584step0; decide +kernel
      have hl : raw14584step0Labels = labelEmbedding7 ∘ raw14584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14584step0 raw14584step0Labels raw14584step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw14585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw14585step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14585step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14585step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14585 raw14585Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw14585 raw14585Labels = mixedMoment B raw14585step0 raw14585step0Labels := by
      have ha : raw14585step0 = (fun i j => raw14585 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14585step0 raw14585; decide +kernel
      have hl : raw14585step0Labels = raw14585Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14585 raw14585Labels permutation194 permutation5
    mixedMoment B raw14585step0 raw14585step0Labels = mixedMoment B raw14585step1 raw14585step1Labels := by
      have ha : raw14585step1 = -raw14585step0 := by apply Matrix.ext; change ∀ i j, raw14585step1 i j = -(raw14585step0 i j); unfold raw14585step1 raw14585step0; decide +kernel
      have hl : raw14585step1Labels = raw14585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14585step1 raw14585step1Labels = mixedMoment B raw14585step2 raw14585step2Labels := by
      have ha : raw14585step2 = raw14585step1 := by apply Matrix.ext; unfold raw14585step2 raw14585step1; decide +kernel
      have hl : raw14585step1Labels = labelEmbedding8 ∘ raw14585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14585step1 raw14585step1Labels raw14585step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw14586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw14586step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14586step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14586step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14586 raw14586Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw14586 raw14586Labels = mixedMoment B raw14586step0 raw14586step0Labels := by
      have ha : raw14586step0 = (fun i j => raw14586 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14586step0 raw14586; decide +kernel
      have hl : raw14586step0Labels = raw14586Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14586 raw14586Labels permutation194 permutation5
    mixedMoment B raw14586step0 raw14586step0Labels = mixedMoment B raw14586step1 raw14586step1Labels := by
      have ha : raw14586step1 = -raw14586step0 := by apply Matrix.ext; change ∀ i j, raw14586step1 i j = -(raw14586step0 i j); unfold raw14586step1 raw14586step0; decide +kernel
      have hl : raw14586step1Labels = raw14586step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14586step1 raw14586step1Labels = mixedMoment B raw14586step2 raw14586step2Labels := by
      have ha : raw14586step2 = raw14586step1 := by apply Matrix.ext; unfold raw14586step2 raw14586step1; decide +kernel
      have hl : raw14586step1Labels = labelEmbedding8 ∘ raw14586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14586step1 raw14586step1Labels raw14586step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw14587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14587step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14587step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14587 raw14587Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw14587 raw14587Labels = mixedMoment B raw14587step0 raw14587step0Labels := by
      have ha : raw14587step0 = (fun i j => raw14587 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14587step0 raw14587; decide +kernel
      have hl : raw14587step0Labels = raw14587Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14587 raw14587Labels permutation206 permutation3
    mixedMoment B raw14587step0 raw14587step0Labels = mixedMoment B raw14587step1 raw14587step1Labels := by
      have ha : raw14587step1 = raw14587step0 := by apply Matrix.ext; unfold raw14587step1 raw14587step0; decide +kernel
      have hl : raw14587step0Labels = labelEmbedding6 ∘ raw14587step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14587step0 raw14587step0Labels raw14587step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw14588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw14588step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14588step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14588step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14588 raw14588Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw14588 raw14588Labels = mixedMoment B raw14588step0 raw14588step0Labels := by
      have ha : raw14588step0 = (fun i j => raw14588 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14588step0 raw14588; decide +kernel
      have hl : raw14588step0Labels = raw14588Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14588 raw14588Labels permutation194 permutation5
    mixedMoment B raw14588step0 raw14588step0Labels = mixedMoment B raw14588step1 raw14588step1Labels := by
      have ha : raw14588step1 = -raw14588step0 := by apply Matrix.ext; change ∀ i j, raw14588step1 i j = -(raw14588step0 i j); unfold raw14588step1 raw14588step0; decide +kernel
      have hl : raw14588step1Labels = raw14588step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14588step1 raw14588step1Labels = mixedMoment B raw14588step2 raw14588step2Labels := by
      have ha : raw14588step2 = raw14588step1 := by apply Matrix.ext; unfold raw14588step2 raw14588step1; decide +kernel
      have hl : raw14588step1Labels = labelEmbedding8 ∘ raw14588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14588step1 raw14588step1Labels raw14588step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw14589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw14589step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14589step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14589step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14589step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14589 raw14589Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw14589 raw14589Labels = mixedMoment B raw14589step0 raw14589step0Labels := by
      have ha : raw14589step0 = (fun i j => raw14589 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14589step0 raw14589; decide +kernel
      have hl : raw14589step0Labels = raw14589Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14589 raw14589Labels permutation194 permutation5
    mixedMoment B raw14589step0 raw14589step0Labels = mixedMoment B raw14589step1 raw14589step1Labels := by
      have ha : raw14589step1 = -raw14589step0 := by apply Matrix.ext; change ∀ i j, raw14589step1 i j = -(raw14589step0 i j); unfold raw14589step1 raw14589step0; decide +kernel
      have hl : raw14589step1Labels = raw14589step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14589step1 raw14589step1Labels = mixedMoment B raw14589step2 raw14589step2Labels := by
      have ha : raw14589step2 = raw14589step1 := by apply Matrix.ext; unfold raw14589step2 raw14589step1; decide +kernel
      have hl : raw14589step1Labels = labelEmbedding8 ∘ raw14589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14589step1 raw14589step1Labels raw14589step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw14590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14590step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14590 raw14590Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw14590 raw14590Labels = mixedMoment B raw14590step0 raw14590step0Labels := by
      have ha : raw14590step0 = (fun i j => raw14590 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14590step0 raw14590; decide +kernel
      have hl : raw14590step0Labels = raw14590Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14590 raw14590Labels permutation158 permutation3
    mixedMoment B raw14590step0 raw14590step0Labels = mixedMoment B raw14590step1 raw14590step1Labels := by
      have ha : raw14590step1 = raw14590step0 := by apply Matrix.ext; unfold raw14590step1 raw14590step0; decide +kernel
      have hl : raw14590step0Labels = labelEmbedding6 ∘ raw14590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14590step0 raw14590step0Labels raw14590step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw14591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14591step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14591 raw14591Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw14591 raw14591Labels = mixedMoment B raw14591step0 raw14591step0Labels := by
      have ha : raw14591step0 = (fun i j => raw14591 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14591step0 raw14591; decide +kernel
      have hl : raw14591step0Labels = raw14591Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14591 raw14591Labels permutation158 permutation3
    mixedMoment B raw14591step0 raw14591step0Labels = mixedMoment B raw14591step1 raw14591step1Labels := by
      have ha : raw14591step1 = raw14591step0 := by apply Matrix.ext; unfold raw14591step1 raw14591step0; decide +kernel
      have hl : raw14591step0Labels = labelEmbedding6 ∘ raw14591step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14591step0 raw14591step0Labels raw14591step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
