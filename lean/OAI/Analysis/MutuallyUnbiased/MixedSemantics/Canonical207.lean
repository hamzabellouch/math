import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26496step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26496step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26496 raw26496Labels = mixedMoment B node4169 node4169Labels := by
  calc
    mixedMoment B raw26496 raw26496Labels = mixedMoment B raw26496step0 raw26496step0Labels := by
      have ha : raw26496step0 = (fun i j => raw26496 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26496step0 raw26496; decide +kernel
      have hl : raw26496step0Labels = raw26496Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26496 raw26496Labels permutation184 permutation3
    mixedMoment B raw26496step0 raw26496step0Labels = mixedMoment B raw26496step1 raw26496step1Labels := by
      have ha : raw26496step1 = raw26496step0 := by apply Matrix.ext; unfold raw26496step1 raw26496step0; decide +kernel
      have hl : raw26496step0Labels = labelEmbedding6 ∘ raw26496step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26496step0 raw26496step0Labels raw26496step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4169 node4169Labels := by rfl

def raw26497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26497step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26497step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26497 raw26497Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26497 raw26497Labels = mixedMoment B raw26497step0 raw26497step0Labels := by
      have ha : raw26497step0 = (fun i j => raw26497 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26497step0 raw26497; decide +kernel
      have hl : raw26497step0Labels = raw26497Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26497 raw26497Labels permutation184 permutation3
    mixedMoment B raw26497step0 raw26497step0Labels = mixedMoment B raw26497step1 raw26497step1Labels := by
      have ha : raw26497step1 = raw26497step0 := by apply Matrix.ext; unfold raw26497step1 raw26497step0; decide +kernel
      have hl : raw26497step0Labels = labelEmbedding6 ∘ raw26497step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26497step0 raw26497step0Labels raw26497step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26498step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26498step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26498 raw26498Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26498 raw26498Labels = mixedMoment B raw26498step0 raw26498step0Labels := by
      have ha : raw26498step0 = (fun i j => raw26498 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26498step0 raw26498; decide +kernel
      have hl : raw26498step0Labels = raw26498Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26498 raw26498Labels permutation208 permutation3
    mixedMoment B raw26498step0 raw26498step0Labels = mixedMoment B raw26498step1 raw26498step1Labels := by
      have ha : raw26498step1 = raw26498step0 := by apply Matrix.ext; unfold raw26498step1 raw26498step0; decide +kernel
      have hl : raw26498step0Labels = labelEmbedding6 ∘ raw26498step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26498step0 raw26498step0Labels raw26498step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26499step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26499step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26499 raw26499Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26499 raw26499Labels = mixedMoment B raw26499step0 raw26499step0Labels := by
      have ha : raw26499step0 = (fun i j => raw26499 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26499step0 raw26499; decide +kernel
      have hl : raw26499step0Labels = raw26499Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26499 raw26499Labels permutation232 permutation3
    mixedMoment B raw26499step0 raw26499step0Labels = mixedMoment B raw26499step1 raw26499step1Labels := by
      have ha : raw26499step1 = raw26499step0 := by apply Matrix.ext; unfold raw26499step1 raw26499step0; decide +kernel
      have hl : raw26499step0Labels = labelEmbedding6 ∘ raw26499step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26499step0 raw26499step0Labels raw26499step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26500step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26500 raw26500Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26500 raw26500Labels = mixedMoment B raw26500step0 raw26500step0Labels := by
      have ha : raw26500step0 = (fun i j => raw26500 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26500step0 raw26500; decide +kernel
      have hl : raw26500step0Labels = raw26500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26500 raw26500Labels permutation246 permutation2
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw26501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26501Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26501step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26501step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26501step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26501 raw26501Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw26501 raw26501Labels = mixedMoment B raw26501step0 raw26501step0Labels := by
      have hz : ∀ j, raw26501 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26501step0 = (fun i j => raw26501 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26501step0 raw26501; decide +kernel
      have hl : raw26501step0Labels = raw26501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26501 raw26501Labels permutation265 hz
    mixedMoment B raw26501step0 raw26501step0Labels = mixedMoment B raw26501step1 raw26501step1Labels := by
      have ha : raw26501step1 = (fun i j => raw26501step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26501step1 raw26501step0; decide +kernel
      have hl : raw26501step1Labels = raw26501step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26501step0 raw26501step0Labels permutation41 permutation3
    mixedMoment B raw26501step1 raw26501step1Labels = mixedMoment B raw26501step2 raw26501step2Labels := by
      have ha : raw26501step2 = raw26501step1 := by apply Matrix.ext; unfold raw26501step2 raw26501step1; decide +kernel
      have hl : raw26501step1Labels = labelEmbedding6 ∘ raw26501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26501step1 raw26501step1Labels raw26501step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4173 node4173Labels := by rfl

def raw26502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26502step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26502step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26502 raw26502Labels = mixedMoment B node4542 node4542Labels := by
  calc
    mixedMoment B raw26502 raw26502Labels = mixedMoment B raw26502step0 raw26502step0Labels := by
      have ha : raw26502step0 = (fun i j => raw26502 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26502step0 raw26502; decide +kernel
      have hl : raw26502step0Labels = raw26502Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26502 raw26502Labels permutation161 permutation3
    mixedMoment B raw26502step0 raw26502step0Labels = mixedMoment B raw26502step1 raw26502step1Labels := by
      have ha : raw26502step1 = raw26502step0 := by apply Matrix.ext; unfold raw26502step1 raw26502step0; decide +kernel
      have hl : raw26502step0Labels = labelEmbedding6 ∘ raw26502step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26502step0 raw26502step0Labels raw26502step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4542 node4542Labels := by rfl

def raw26503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26503step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26503step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26503step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26503 raw26503Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26503 raw26503Labels = mixedMoment B raw26503step0 raw26503step0Labels := by
      have hz : ∀ j, raw26503 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26503step0 = (fun i j => raw26503 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26503step0 raw26503; decide +kernel
      have hl : raw26503step0Labels = raw26503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26503 raw26503Labels permutation265 hz
    mixedMoment B raw26503step0 raw26503step0Labels = mixedMoment B raw26503step1 raw26503step1Labels := by
      have ha : raw26503step1 = (fun i j => raw26503step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26503step1 raw26503step0; decide +kernel
      have hl : raw26503step1Labels = raw26503step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26503step0 raw26503step0Labels permutation41 permutation3
    mixedMoment B raw26503step1 raw26503step1Labels = mixedMoment B raw26503step2 raw26503step2Labels := by
      have ha : raw26503step2 = raw26503step1 := by apply Matrix.ext; unfold raw26503step2 raw26503step1; decide +kernel
      have hl : raw26503step1Labels = labelEmbedding6 ∘ raw26503step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26503step1 raw26503step1Labels raw26503step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw26504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26504step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26504step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26504step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26504 raw26504Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26504 raw26504Labels = mixedMoment B raw26504step0 raw26504step0Labels := by
      have hz : ∀ j, raw26504 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26504step0 = (fun i j => raw26504 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26504step0 raw26504; decide +kernel
      have hl : raw26504step0Labels = raw26504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26504 raw26504Labels permutation265 hz
    mixedMoment B raw26504step0 raw26504step0Labels = mixedMoment B raw26504step1 raw26504step1Labels := by
      have ha : raw26504step1 = (fun i j => raw26504step0 (permutation47 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26504step1 raw26504step0; decide +kernel
      have hl : raw26504step1Labels = raw26504step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26504step0 raw26504step0Labels permutation47 permutation3
    mixedMoment B raw26504step1 raw26504step1Labels = mixedMoment B raw26504step2 raw26504step2Labels := by
      have ha : raw26504step2 = raw26504step1 := by apply Matrix.ext; unfold raw26504step2 raw26504step1; decide +kernel
      have hl : raw26504step1Labels = labelEmbedding6 ∘ raw26504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26504step1 raw26504step1Labels raw26504step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw26505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26505step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26505 raw26505Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26505 raw26505Labels = mixedMoment B raw26505step0 raw26505step0Labels := by
      have hz : ∀ j, raw26505 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26505step0 = (fun i j => raw26505 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26505step0 raw26505; decide +kernel
      have hl : raw26505step0Labels = raw26505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26505 raw26505Labels permutation265 hz
    mixedMoment B raw26505step0 raw26505step0Labels = mixedMoment B raw26505step1 raw26505step1Labels := by
      have ha : raw26505step1 = (fun i j => raw26505step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26505step1 raw26505step0; decide +kernel
      have hl : raw26505step1Labels = raw26505step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26505step0 raw26505step0Labels permutation53 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw26506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26506step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26506step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26506 raw26506Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw26506 raw26506Labels = mixedMoment B raw26506step0 raw26506step0Labels := by
      have hz : ∀ j, raw26506 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26506step0 = (fun i j => raw26506 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26506step0 raw26506; decide +kernel
      have hl : raw26506step0Labels = raw26506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26506 raw26506Labels permutation265 hz
    mixedMoment B raw26506step0 raw26506step0Labels = mixedMoment B raw26506step1 raw26506step1Labels := by
      have ha : raw26506step1 = (fun i j => raw26506step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26506step1 raw26506step0; decide +kernel
      have hl : raw26506step1Labels = raw26506step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26506step0 raw26506step0Labels permutation35 permutation3
    mixedMoment B raw26506step1 raw26506step1Labels = mixedMoment B raw26506step2 raw26506step2Labels := by
      have ha : raw26506step2 = raw26506step1 := by apply Matrix.ext; unfold raw26506step2 raw26506step1; decide +kernel
      have hl : raw26506step1Labels = labelEmbedding6 ∘ raw26506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26506step1 raw26506step1Labels raw26506step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4173 node4173Labels := by rfl

def raw26507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26507step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26507 raw26507Labels = mixedMoment B node4542 node4542Labels := by
  calc
    mixedMoment B raw26507 raw26507Labels = mixedMoment B raw26507step0 raw26507step0Labels := by
      have ha : raw26507step0 = (fun i j => raw26507 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26507step0 raw26507; decide +kernel
      have hl : raw26507step0Labels = raw26507Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26507 raw26507Labels permutation155 permutation3
    mixedMoment B raw26507step0 raw26507step0Labels = mixedMoment B raw26507step1 raw26507step1Labels := by
      have ha : raw26507step1 = raw26507step0 := by apply Matrix.ext; unfold raw26507step1 raw26507step0; decide +kernel
      have hl : raw26507step0Labels = labelEmbedding6 ∘ raw26507step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26507step0 raw26507step0Labels raw26507step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4542 node4542Labels := by rfl

def raw26508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26508step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26508step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26508 raw26508Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26508 raw26508Labels = mixedMoment B raw26508step0 raw26508step0Labels := by
      have hz : ∀ j, raw26508 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26508step0 = (fun i j => raw26508 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26508step0 raw26508; decide +kernel
      have hl : raw26508step0Labels = raw26508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26508 raw26508Labels permutation265 hz
    mixedMoment B raw26508step0 raw26508step0Labels = mixedMoment B raw26508step1 raw26508step1Labels := by
      have ha : raw26508step1 = (fun i j => raw26508step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26508step1 raw26508step0; decide +kernel
      have hl : raw26508step1Labels = raw26508step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26508step0 raw26508step0Labels permutation35 permutation3
    mixedMoment B raw26508step1 raw26508step1Labels = mixedMoment B raw26508step2 raw26508step2Labels := by
      have ha : raw26508step2 = raw26508step1 := by apply Matrix.ext; unfold raw26508step2 raw26508step1; decide +kernel
      have hl : raw26508step1Labels = labelEmbedding6 ∘ raw26508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26508step1 raw26508step1Labels raw26508step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw26509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26509step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26509step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26509 raw26509Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26509 raw26509Labels = mixedMoment B raw26509step0 raw26509step0Labels := by
      have hz : ∀ j, raw26509 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26509step0 = (fun i j => raw26509 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26509step0 raw26509; decide +kernel
      have hl : raw26509step0Labels = raw26509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26509 raw26509Labels permutation265 hz
    mixedMoment B raw26509step0 raw26509step0Labels = mixedMoment B raw26509step1 raw26509step1Labels := by
      have ha : raw26509step1 = (fun i j => raw26509step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26509step1 raw26509step0; decide +kernel
      have hl : raw26509step1Labels = raw26509step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26509step0 raw26509step0Labels permutation45 permutation3
    mixedMoment B raw26509step1 raw26509step1Labels = mixedMoment B raw26509step2 raw26509step2Labels := by
      have ha : raw26509step2 = raw26509step1 := by apply Matrix.ext; unfold raw26509step2 raw26509step1; decide +kernel
      have hl : raw26509step1Labels = labelEmbedding6 ∘ raw26509step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26509step1 raw26509step1Labels raw26509step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw26510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26510 raw26510Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26510 raw26510Labels = mixedMoment B raw26510step0 raw26510step0Labels := by
      have hz : ∀ j, raw26510 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26510step0 = (fun i j => raw26510 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26510step0 raw26510; decide +kernel
      have hl : raw26510step0Labels = raw26510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26510 raw26510Labels permutation265 hz
    mixedMoment B raw26510step0 raw26510step0Labels = mixedMoment B raw26510step1 raw26510step1Labels := by
      have ha : raw26510step1 = (fun i j => raw26510step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26510step1 raw26510step0; decide +kernel
      have hl : raw26510step1Labels = raw26510step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26510step0 raw26510step0Labels permutation51 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw26511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26511step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26511step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26511 raw26511Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw26511 raw26511Labels = mixedMoment B raw26511step0 raw26511step0Labels := by
      have hz : ∀ j, raw26511 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26511step0 = (fun i j => raw26511 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26511step0 raw26511; decide +kernel
      have hl : raw26511step0Labels = raw26511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26511 raw26511Labels permutation265 hz
    mixedMoment B raw26511step0 raw26511step0Labels = mixedMoment B raw26511step1 raw26511step1Labels := by
      have ha : raw26511step1 = (fun i j => raw26511step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26511step1 raw26511step0; decide +kernel
      have hl : raw26511step1Labels = raw26511step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26511step0 raw26511step0Labels permutation33 permutation3
    mixedMoment B raw26511step1 raw26511step1Labels = mixedMoment B raw26511step2 raw26511step2Labels := by
      have ha : raw26511step2 = raw26511step1 := by apply Matrix.ext; unfold raw26511step2 raw26511step1; decide +kernel
      have hl : raw26511step1Labels = labelEmbedding6 ∘ raw26511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26511step1 raw26511step1Labels raw26511step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4173 node4173Labels := by rfl

def raw26512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26512step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26512step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26512 raw26512Labels = mixedMoment B node4542 node4542Labels := by
  calc
    mixedMoment B raw26512 raw26512Labels = mixedMoment B raw26512step0 raw26512step0Labels := by
      have ha : raw26512step0 = (fun i j => raw26512 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26512step0 raw26512; decide +kernel
      have hl : raw26512step0Labels = raw26512Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26512 raw26512Labels permutation153 permutation3
    mixedMoment B raw26512step0 raw26512step0Labels = mixedMoment B raw26512step1 raw26512step1Labels := by
      have ha : raw26512step1 = raw26512step0 := by apply Matrix.ext; unfold raw26512step1 raw26512step0; decide +kernel
      have hl : raw26512step0Labels = labelEmbedding6 ∘ raw26512step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26512step0 raw26512step0Labels raw26512step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4542 node4542Labels := by rfl

def raw26513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26513step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26513step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26513 raw26513Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26513 raw26513Labels = mixedMoment B raw26513step0 raw26513step0Labels := by
      have hz : ∀ j, raw26513 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26513step0 = (fun i j => raw26513 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26513step0 raw26513; decide +kernel
      have hl : raw26513step0Labels = raw26513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26513 raw26513Labels permutation265 hz
    mixedMoment B raw26513step0 raw26513step0Labels = mixedMoment B raw26513step1 raw26513step1Labels := by
      have ha : raw26513step1 = (fun i j => raw26513step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26513step1 raw26513step0; decide +kernel
      have hl : raw26513step1Labels = raw26513step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26513step0 raw26513step0Labels permutation33 permutation3
    mixedMoment B raw26513step1 raw26513step1Labels = mixedMoment B raw26513step2 raw26513step2Labels := by
      have ha : raw26513step2 = raw26513step1 := by apply Matrix.ext; unfold raw26513step2 raw26513step1; decide +kernel
      have hl : raw26513step1Labels = labelEmbedding6 ∘ raw26513step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26513step1 raw26513step1Labels raw26513step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw26514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26514step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26514step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26514 raw26514Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26514 raw26514Labels = mixedMoment B raw26514step0 raw26514step0Labels := by
      have hz : ∀ j, raw26514 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26514step0 = (fun i j => raw26514 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26514step0 raw26514; decide +kernel
      have hl : raw26514step0Labels = raw26514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26514 raw26514Labels permutation265 hz
    mixedMoment B raw26514step0 raw26514step0Labels = mixedMoment B raw26514step1 raw26514step1Labels := by
      have ha : raw26514step1 = (fun i j => raw26514step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26514step1 raw26514step0; decide +kernel
      have hl : raw26514step1Labels = raw26514step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26514step0 raw26514step0Labels permutation39 permutation3
    mixedMoment B raw26514step1 raw26514step1Labels = mixedMoment B raw26514step2 raw26514step2Labels := by
      have ha : raw26514step2 = raw26514step1 := by apply Matrix.ext; unfold raw26514step2 raw26514step1; decide +kernel
      have hl : raw26514step1Labels = labelEmbedding6 ∘ raw26514step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26514step1 raw26514step1Labels raw26514step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw26515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26515 raw26515Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26515 raw26515Labels = mixedMoment B raw26515step0 raw26515step0Labels := by
      have hz : ∀ j, raw26515 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26515step0 = (fun i j => raw26515 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26515step0 raw26515; decide +kernel
      have hl : raw26515step0Labels = raw26515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26515 raw26515Labels permutation265 hz
    mixedMoment B raw26515step0 raw26515step0Labels = mixedMoment B raw26515step1 raw26515step1Labels := by
      have ha : raw26515step1 = (fun i j => raw26515step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26515step1 raw26515step0; decide +kernel
      have hl : raw26515step1Labels = raw26515step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26515step0 raw26515step0Labels permutation50 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw26516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26516step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26516step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26516 raw26516Labels = mixedMoment B node4170 node4170Labels := by
  calc
    mixedMoment B raw26516 raw26516Labels = mixedMoment B raw26516step0 raw26516step0Labels := by
      have hz : ∀ j, raw26516 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26516step0 = (fun i j => raw26516 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26516step0 raw26516; decide +kernel
      have hl : raw26516step0Labels = raw26516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26516 raw26516Labels permutation265 hz
    mixedMoment B raw26516step0 raw26516step0Labels = mixedMoment B raw26516step1 raw26516step1Labels := by
      have ha : raw26516step1 = (fun i j => raw26516step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26516step1 raw26516step0; decide +kernel
      have hl : raw26516step1Labels = raw26516step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26516step0 raw26516step0Labels permutation32 permutation3
    mixedMoment B raw26516step1 raw26516step1Labels = mixedMoment B raw26516step2 raw26516step2Labels := by
      have ha : raw26516step2 = raw26516step1 := by apply Matrix.ext; unfold raw26516step2 raw26516step1; decide +kernel
      have hl : raw26516step1Labels = labelEmbedding6 ∘ raw26516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26516step1 raw26516step1Labels raw26516step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4170 node4170Labels := by rfl

def raw26517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26517step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26517step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26517 raw26517Labels = mixedMoment B node4540 node4540Labels := by
  calc
    mixedMoment B raw26517 raw26517Labels = mixedMoment B raw26517step0 raw26517step0Labels := by
      have ha : raw26517step0 = (fun i j => raw26517 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26517step0 raw26517; decide +kernel
      have hl : raw26517step0Labels = raw26517Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26517 raw26517Labels permutation152 permutation3
    mixedMoment B raw26517step0 raw26517step0Labels = mixedMoment B raw26517step1 raw26517step1Labels := by
      have ha : raw26517step1 = raw26517step0 := by apply Matrix.ext; unfold raw26517step1 raw26517step0; decide +kernel
      have hl : raw26517step0Labels = labelEmbedding6 ∘ raw26517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26517step0 raw26517step0Labels raw26517step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4540 node4540Labels := by rfl

def raw26518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26518step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26518step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26518 raw26518Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw26518 raw26518Labels = mixedMoment B raw26518step0 raw26518step0Labels := by
      have hz : ∀ j, raw26518 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26518step0 = (fun i j => raw26518 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26518step0 raw26518; decide +kernel
      have hl : raw26518step0Labels = raw26518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26518 raw26518Labels permutation265 hz
    mixedMoment B raw26518step0 raw26518step0Labels = mixedMoment B raw26518step1 raw26518step1Labels := by
      have ha : raw26518step1 = (fun i j => raw26518step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26518step1 raw26518step0; decide +kernel
      have hl : raw26518step1Labels = raw26518step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26518step0 raw26518step0Labels permutation44 permutation3
    mixedMoment B raw26518step1 raw26518step1Labels = mixedMoment B raw26518step2 raw26518step2Labels := by
      have ha : raw26518step2 = raw26518step1 := by apply Matrix.ext; unfold raw26518step2 raw26518step1; decide +kernel
      have hl : raw26518step1Labels = labelEmbedding6 ∘ raw26518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26518step1 raw26518step1Labels raw26518step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw26519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26519 raw26519Labels = mixedMoment B node2957 node2957Labels := by
  calc
    mixedMoment B raw26519 raw26519Labels = mixedMoment B raw26519step0 raw26519step0Labels := by
      have ha : raw26519step0 = (fun i j => raw26519 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26519step0 raw26519; decide +kernel
      have hl : raw26519step0Labels = raw26519Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26519 raw26519Labels permutation152 permutation3
    _ = mixedMoment B node2957 node2957Labels := by rfl

def raw26520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26520step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26520 raw26520Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw26520 raw26520Labels = mixedMoment B raw26520step0 raw26520step0Labels := by
      have hz : ∀ j, raw26520 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26520step0 = (fun i j => raw26520 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26520step0 raw26520; decide +kernel
      have hl : raw26520step0Labels = raw26520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26520 raw26520Labels permutation265 hz
    mixedMoment B raw26520step0 raw26520step0Labels = mixedMoment B raw26520step1 raw26520step1Labels := by
      have ha : raw26520step1 = (fun i j => raw26520step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26520step1 raw26520step0; decide +kernel
      have hl : raw26520step1Labels = raw26520step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26520step0 raw26520step0Labels permutation44 permutation3
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw26521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26521Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26521step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw26521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26521 raw26521Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw26521 raw26521Labels = mixedMoment B raw26521step0 raw26521step0Labels := by
      have hz : ∀ j, raw26521 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26521step0 = (fun i j => raw26521 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26521step0 raw26521; decide +kernel
      have hl : raw26521step0Labels = raw26521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26521 raw26521Labels permutation265 hz
    mixedMoment B raw26521step0 raw26521step0Labels = mixedMoment B raw26521step1 raw26521step1Labels := by
      have ha : raw26521step1 = (fun i j => raw26521step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26521step1 raw26521step0; decide +kernel
      have hl : raw26521step1Labels = raw26521step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26521step0 raw26521step0Labels permutation50 permutation3
    _ = mixedMoment B node3111 node3111Labels := by rfl

def raw26522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26522Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26522 raw26522Labels = mixedMoment B node597 node597Labels := by
  calc
    mixedMoment B raw26522 raw26522Labels = mixedMoment B raw26522step0 raw26522step0Labels := by
      have ha : raw26522step0 = (fun i j => raw26522 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26522step0 raw26522; decide +kernel
      have hl : raw26522step0Labels = raw26522Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26522 raw26522Labels permutation184 permutation3
    _ = mixedMoment B node597 node597Labels := by rfl

def raw26523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26523Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26523 raw26523Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw26523 raw26523Labels = mixedMoment B raw26523step0 raw26523step0Labels := by
      have ha : raw26523step0 = (fun i j => raw26523 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26523step0 raw26523; decide +kernel
      have hl : raw26523step0Labels = raw26523Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26523 raw26523Labels permutation184 permutation3
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw26524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26524Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26524 raw26524Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw26524 raw26524Labels = mixedMoment B raw26524step0 raw26524step0Labels := by
      have ha : raw26524step0 = (fun i j => raw26524 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26524step0 raw26524; decide +kernel
      have hl : raw26524step0Labels = raw26524Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26524 raw26524Labels permutation208 permutation3
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw26525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26525 raw26525Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw26525 raw26525Labels = mixedMoment B raw26525step0 raw26525step0Labels := by
      have ha : raw26525step0 = (fun i j => raw26525 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26525step0 raw26525; decide +kernel
      have hl : raw26525step0Labels = raw26525Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26525 raw26525Labels permutation232 permutation3
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw26526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26526 raw26526Labels = mixedMoment B node1265 node1265Labels := by
  calc
    mixedMoment B raw26526 raw26526Labels = mixedMoment B raw26526step0 raw26526step0Labels := by
      have ha : raw26526step0 = (fun i j => raw26526 (permutation255 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26526step0 raw26526; decide +kernel
      have hl : raw26526step0Labels = raw26526Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26526 raw26526Labels permutation255 permutation3
    _ = mixedMoment B node1265 node1265Labels := by rfl

def raw26527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26527step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26527 raw26527Labels = mixedMoment B node601 node601Labels := by
  calc
    mixedMoment B raw26527 raw26527Labels = mixedMoment B raw26527step0 raw26527step0Labels := by
      have hz : ∀ j, raw26527 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26527step0 = (fun i j => raw26527 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26527step0 raw26527; decide +kernel
      have hl : raw26527step0Labels = raw26527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26527 raw26527Labels permutation265 hz
    mixedMoment B raw26527step0 raw26527step0Labels = mixedMoment B raw26527step1 raw26527step1Labels := by
      have ha : raw26527step1 = (fun i j => raw26527step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26527step1 raw26527step0; decide +kernel
      have hl : raw26527step1Labels = raw26527step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26527step0 raw26527step0Labels permutation41 permutation3
    _ = mixedMoment B node601 node601Labels := by rfl

def raw26528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26528Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26528 raw26528Labels = mixedMoment B node1127 node1127Labels := by
  calc
    mixedMoment B raw26528 raw26528Labels = mixedMoment B raw26528step0 raw26528step0Labels := by
      have ha : raw26528step0 = (fun i j => raw26528 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26528step0 raw26528; decide +kernel
      have hl : raw26528step0Labels = raw26528Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26528 raw26528Labels permutation161 permutation3
    _ = mixedMoment B node1127 node1127Labels := by rfl

def raw26529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26529Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26529step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26529 raw26529Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw26529 raw26529Labels = mixedMoment B raw26529step0 raw26529step0Labels := by
      have hz : ∀ j, raw26529 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26529step0 = (fun i j => raw26529 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26529step0 raw26529; decide +kernel
      have hl : raw26529step0Labels = raw26529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26529 raw26529Labels permutation265 hz
    mixedMoment B raw26529step0 raw26529step0Labels = mixedMoment B raw26529step1 raw26529step1Labels := by
      have ha : raw26529step1 = (fun i j => raw26529step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26529step1 raw26529step0; decide +kernel
      have hl : raw26529step1Labels = raw26529step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26529step0 raw26529step0Labels permutation41 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw26530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26530Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26530step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26530 raw26530Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw26530 raw26530Labels = mixedMoment B raw26530step0 raw26530step0Labels := by
      have hz : ∀ j, raw26530 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26530step0 = (fun i j => raw26530 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26530step0 raw26530; decide +kernel
      have hl : raw26530step0Labels = raw26530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26530 raw26530Labels permutation265 hz
    mixedMoment B raw26530step0 raw26530step0Labels = mixedMoment B raw26530step1 raw26530step1Labels := by
      have ha : raw26530step1 = (fun i j => raw26530step0 (permutation47 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26530step1 raw26530step0; decide +kernel
      have hl : raw26530step1Labels = raw26530step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26530step0 raw26530step0Labels permutation47 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw26531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26531 raw26531Labels = mixedMoment B node1266 node1266Labels := by
  calc
    mixedMoment B raw26531 raw26531Labels = mixedMoment B raw26531step0 raw26531step0Labels := by
      have hz : ∀ j, raw26531 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26531step0 = (fun i j => raw26531 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26531step0 raw26531; decide +kernel
      have hl : raw26531step0Labels = raw26531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26531 raw26531Labels permutation265 hz
    mixedMoment B raw26531step0 raw26531step0Labels = mixedMoment B raw26531step1 raw26531step1Labels := by
      have ha : raw26531step1 = (fun i j => raw26531step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26531step1 raw26531step0; decide +kernel
      have hl : raw26531step1Labels = raw26531step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26531step0 raw26531step0Labels permutation53 permutation3
    _ = mixedMoment B node1266 node1266Labels := by rfl

def raw26532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26532 raw26532Labels = mixedMoment B node601 node601Labels := by
  calc
    mixedMoment B raw26532 raw26532Labels = mixedMoment B raw26532step0 raw26532step0Labels := by
      have hz : ∀ j, raw26532 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26532step0 = (fun i j => raw26532 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26532step0 raw26532; decide +kernel
      have hl : raw26532step0Labels = raw26532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26532 raw26532Labels permutation265 hz
    mixedMoment B raw26532step0 raw26532step0Labels = mixedMoment B raw26532step1 raw26532step1Labels := by
      have ha : raw26532step1 = (fun i j => raw26532step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26532step1 raw26532step0; decide +kernel
      have hl : raw26532step1Labels = raw26532step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26532step0 raw26532step0Labels permutation35 permutation3
    _ = mixedMoment B node601 node601Labels := by rfl

def raw26533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26533 raw26533Labels = mixedMoment B node1127 node1127Labels := by
  calc
    mixedMoment B raw26533 raw26533Labels = mixedMoment B raw26533step0 raw26533step0Labels := by
      have ha : raw26533step0 = (fun i j => raw26533 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26533step0 raw26533; decide +kernel
      have hl : raw26533step0Labels = raw26533Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26533 raw26533Labels permutation155 permutation3
    _ = mixedMoment B node1127 node1127Labels := by rfl

def raw26534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26534 raw26534Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw26534 raw26534Labels = mixedMoment B raw26534step0 raw26534step0Labels := by
      have hz : ∀ j, raw26534 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26534step0 = (fun i j => raw26534 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26534step0 raw26534; decide +kernel
      have hl : raw26534step0Labels = raw26534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26534 raw26534Labels permutation265 hz
    mixedMoment B raw26534step0 raw26534step0Labels = mixedMoment B raw26534step1 raw26534step1Labels := by
      have ha : raw26534step1 = (fun i j => raw26534step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26534step1 raw26534step0; decide +kernel
      have hl : raw26534step1Labels = raw26534step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26534step0 raw26534step0Labels permutation35 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw26535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26535 raw26535Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw26535 raw26535Labels = mixedMoment B raw26535step0 raw26535step0Labels := by
      have hz : ∀ j, raw26535 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26535step0 = (fun i j => raw26535 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26535step0 raw26535; decide +kernel
      have hl : raw26535step0Labels = raw26535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26535 raw26535Labels permutation265 hz
    mixedMoment B raw26535step0 raw26535step0Labels = mixedMoment B raw26535step1 raw26535step1Labels := by
      have ha : raw26535step1 = (fun i j => raw26535step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26535step1 raw26535step0; decide +kernel
      have hl : raw26535step1Labels = raw26535step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26535step0 raw26535step0Labels permutation45 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw26536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26536 raw26536Labels = mixedMoment B node1266 node1266Labels := by
  calc
    mixedMoment B raw26536 raw26536Labels = mixedMoment B raw26536step0 raw26536step0Labels := by
      have hz : ∀ j, raw26536 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26536step0 = (fun i j => raw26536 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26536step0 raw26536; decide +kernel
      have hl : raw26536step0Labels = raw26536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26536 raw26536Labels permutation265 hz
    mixedMoment B raw26536step0 raw26536step0Labels = mixedMoment B raw26536step1 raw26536step1Labels := by
      have ha : raw26536step1 = (fun i j => raw26536step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26536step1 raw26536step0; decide +kernel
      have hl : raw26536step1Labels = raw26536step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26536step0 raw26536step0Labels permutation51 permutation3
    _ = mixedMoment B node1266 node1266Labels := by rfl

def raw26537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26537 raw26537Labels = mixedMoment B node601 node601Labels := by
  calc
    mixedMoment B raw26537 raw26537Labels = mixedMoment B raw26537step0 raw26537step0Labels := by
      have hz : ∀ j, raw26537 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26537step0 = (fun i j => raw26537 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26537step0 raw26537; decide +kernel
      have hl : raw26537step0Labels = raw26537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26537 raw26537Labels permutation265 hz
    mixedMoment B raw26537step0 raw26537step0Labels = mixedMoment B raw26537step1 raw26537step1Labels := by
      have ha : raw26537step1 = (fun i j => raw26537step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26537step1 raw26537step0; decide +kernel
      have hl : raw26537step1Labels = raw26537step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26537step0 raw26537step0Labels permutation33 permutation3
    _ = mixedMoment B node601 node601Labels := by rfl

def raw26538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26538 raw26538Labels = mixedMoment B node1127 node1127Labels := by
  calc
    mixedMoment B raw26538 raw26538Labels = mixedMoment B raw26538step0 raw26538step0Labels := by
      have ha : raw26538step0 = (fun i j => raw26538 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26538step0 raw26538; decide +kernel
      have hl : raw26538step0Labels = raw26538Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26538 raw26538Labels permutation153 permutation3
    _ = mixedMoment B node1127 node1127Labels := by rfl

def raw26539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26539 raw26539Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw26539 raw26539Labels = mixedMoment B raw26539step0 raw26539step0Labels := by
      have hz : ∀ j, raw26539 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26539step0 = (fun i j => raw26539 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26539step0 raw26539; decide +kernel
      have hl : raw26539step0Labels = raw26539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26539 raw26539Labels permutation265 hz
    mixedMoment B raw26539step0 raw26539step0Labels = mixedMoment B raw26539step1 raw26539step1Labels := by
      have ha : raw26539step1 = (fun i j => raw26539step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26539step1 raw26539step0; decide +kernel
      have hl : raw26539step1Labels = raw26539step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26539step0 raw26539step0Labels permutation33 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw26540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26540 raw26540Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw26540 raw26540Labels = mixedMoment B raw26540step0 raw26540step0Labels := by
      have hz : ∀ j, raw26540 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26540step0 = (fun i j => raw26540 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26540step0 raw26540; decide +kernel
      have hl : raw26540step0Labels = raw26540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26540 raw26540Labels permutation265 hz
    mixedMoment B raw26540step0 raw26540step0Labels = mixedMoment B raw26540step1 raw26540step1Labels := by
      have ha : raw26540step1 = (fun i j => raw26540step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26540step1 raw26540step0; decide +kernel
      have hl : raw26540step1Labels = raw26540step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26540step0 raw26540step0Labels permutation39 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw26541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26541step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26541 raw26541Labels = mixedMoment B node1266 node1266Labels := by
  calc
    mixedMoment B raw26541 raw26541Labels = mixedMoment B raw26541step0 raw26541step0Labels := by
      have hz : ∀ j, raw26541 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26541step0 = (fun i j => raw26541 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26541step0 raw26541; decide +kernel
      have hl : raw26541step0Labels = raw26541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26541 raw26541Labels permutation265 hz
    mixedMoment B raw26541step0 raw26541step0Labels = mixedMoment B raw26541step1 raw26541step1Labels := by
      have ha : raw26541step1 = (fun i j => raw26541step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26541step1 raw26541step0; decide +kernel
      have hl : raw26541step1Labels = raw26541step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26541step0 raw26541step0Labels permutation50 permutation3
    _ = mixedMoment B node1266 node1266Labels := by rfl

def raw26542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26542 raw26542Labels = mixedMoment B node598 node598Labels := by
  calc
    mixedMoment B raw26542 raw26542Labels = mixedMoment B raw26542step0 raw26542step0Labels := by
      have hz : ∀ j, raw26542 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26542step0 = (fun i j => raw26542 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26542step0 raw26542; decide +kernel
      have hl : raw26542step0Labels = raw26542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26542 raw26542Labels permutation265 hz
    mixedMoment B raw26542step0 raw26542step0Labels = mixedMoment B raw26542step1 raw26542step1Labels := by
      have ha : raw26542step1 = (fun i j => raw26542step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26542step1 raw26542step0; decide +kernel
      have hl : raw26542step1Labels = raw26542step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26542step0 raw26542step0Labels permutation32 permutation3
    _ = mixedMoment B node598 node598Labels := by rfl

def raw26543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26543 raw26543Labels = mixedMoment B node1125 node1125Labels := by
  calc
    mixedMoment B raw26543 raw26543Labels = mixedMoment B raw26543step0 raw26543step0Labels := by
      have ha : raw26543step0 = (fun i j => raw26543 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26543step0 raw26543; decide +kernel
      have hl : raw26543step0Labels = raw26543Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26543 raw26543Labels permutation152 permutation3
    _ = mixedMoment B node1125 node1125Labels := by rfl

def raw26544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26544 raw26544Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw26544 raw26544Labels = mixedMoment B raw26544step0 raw26544step0Labels := by
      have hz : ∀ j, raw26544 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26544step0 = (fun i j => raw26544 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26544step0 raw26544; decide +kernel
      have hl : raw26544step0Labels = raw26544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26544 raw26544Labels permutation265 hz
    mixedMoment B raw26544step0 raw26544step0Labels = mixedMoment B raw26544step1 raw26544step1Labels := by
      have ha : raw26544step1 = (fun i j => raw26544step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26544step1 raw26544step0; decide +kernel
      have hl : raw26544step1Labels = raw26544step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26544step0 raw26544step0Labels permutation44 permutation3
    _ = mixedMoment B node1234 node1234Labels := by rfl

def raw26545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26545step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26545step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26545 raw26545Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw26545 raw26545Labels = mixedMoment B raw26545step0 raw26545step0Labels := by
      have ha : raw26545step0 = (fun i j => raw26545 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26545step0 raw26545; decide +kernel
      have hl : raw26545step0Labels = raw26545Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26545 raw26545Labels permutation246 permutation7
    mixedMoment B raw26545step0 raw26545step0Labels = mixedMoment B raw26545step1 raw26545step1Labels := by
      have ha : raw26545step1 = -raw26545step0 := by apply Matrix.ext; change ∀ i j, raw26545step1 i j = -(raw26545step0 i j); unfold raw26545step1 raw26545step0; decide +kernel
      have hl : raw26545step1Labels = raw26545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26545step1 raw26545step1Labels = mixedMoment B raw26545step2 raw26545step2Labels := by
      have ha : raw26545step2 = raw26545step1 := by apply Matrix.ext; unfold raw26545step2 raw26545step1; decide +kernel
      have hl : raw26545step1Labels = labelEmbedding1 ∘ raw26545step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26545step1 raw26545step1Labels raw26545step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

def raw26546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26546step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26546step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26546 raw26546Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw26546 raw26546Labels = mixedMoment B raw26546step0 raw26546step0Labels := by
      have hz : ∀ j, raw26546 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26546step0 = (fun i j => raw26546 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26546step0 raw26546; decide +kernel
      have hl : raw26546step0Labels = raw26546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26546 raw26546Labels permutation265 hz
    mixedMoment B raw26546step0 raw26546step0Labels = mixedMoment B raw26546step1 raw26546step1Labels := by
      have ha : raw26546step1 = (fun i j => raw26546step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26546step1 raw26546step0; decide +kernel
      have hl : raw26546step1Labels = raw26546step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26546step0 raw26546step0Labels permutation54 permutation7
    mixedMoment B raw26546step1 raw26546step1Labels = mixedMoment B raw26546step2 raw26546step2Labels := by
      have ha : raw26546step2 = -raw26546step1 := by apply Matrix.ext; change ∀ i j, raw26546step2 i j = -(raw26546step1 i j); unfold raw26546step2 raw26546step1; decide +kernel
      have hl : raw26546step2Labels = raw26546step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26546step2 raw26546step2Labels = mixedMoment B raw26546step3 raw26546step3Labels := by
      have ha : raw26546step3 = raw26546step2 := by apply Matrix.ext; unfold raw26546step3 raw26546step2; decide +kernel
      have hl : raw26546step2Labels = labelEmbedding1 ∘ raw26546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26546step2 raw26546step2Labels raw26546step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw26547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26547Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26547step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26547step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26547step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26547step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26547step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26547 raw26547Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw26547 raw26547Labels = mixedMoment B raw26547step0 raw26547step0Labels := by
      have hz : ∀ j, raw26547 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26547step0 = (fun i j => raw26547 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26547step0 raw26547; decide +kernel
      have hl : raw26547step0Labels = raw26547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26547 raw26547Labels permutation265 hz
    mixedMoment B raw26547step0 raw26547step0Labels = mixedMoment B raw26547step1 raw26547step1Labels := by
      have ha : raw26547step1 = (fun i j => raw26547step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26547step1 raw26547step0; decide +kernel
      have hl : raw26547step1Labels = raw26547step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26547step0 raw26547step0Labels permutation50 permutation7
    mixedMoment B raw26547step1 raw26547step1Labels = mixedMoment B raw26547step2 raw26547step2Labels := by
      have ha : raw26547step2 = -raw26547step1 := by apply Matrix.ext; change ∀ i j, raw26547step2 i j = -(raw26547step1 i j); unfold raw26547step2 raw26547step1; decide +kernel
      have hl : raw26547step2Labels = raw26547step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26547step2 raw26547step2Labels = mixedMoment B raw26547step3 raw26547step3Labels := by
      have ha : raw26547step3 = raw26547step2 := by apply Matrix.ext; unfold raw26547step3 raw26547step2; decide +kernel
      have hl : raw26547step2Labels = labelEmbedding1 ∘ raw26547step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26547step2 raw26547step2Labels raw26547step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

def raw26548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26548step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26548step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26548 raw26548Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw26548 raw26548Labels = mixedMoment B raw26548step0 raw26548step0Labels := by
      have ha : raw26548step0 = (fun i j => raw26548 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26548step0 raw26548; decide +kernel
      have hl : raw26548step0Labels = raw26548Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26548 raw26548Labels permutation184 permutation5
    mixedMoment B raw26548step0 raw26548step0Labels = mixedMoment B raw26548step1 raw26548step1Labels := by
      have ha : raw26548step1 = -raw26548step0 := by apply Matrix.ext; change ∀ i j, raw26548step1 i j = -(raw26548step0 i j); unfold raw26548step1 raw26548step0; decide +kernel
      have hl : raw26548step1Labels = raw26548step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26548step1 raw26548step1Labels = mixedMoment B raw26548step2 raw26548step2Labels := by
      have ha : raw26548step2 = raw26548step1 := by apply Matrix.ext; unfold raw26548step2 raw26548step1; decide +kernel
      have hl : raw26548step1Labels = labelEmbedding1 ∘ raw26548step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26548step1 raw26548step1Labels raw26548step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1502 node1502Labels := by rfl

def raw26549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26549Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26549step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26549step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26549 raw26549Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26549 raw26549Labels = mixedMoment B raw26549step0 raw26549step0Labels := by
      have ha : raw26549step0 = (fun i j => raw26549 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26549step0 raw26549; decide +kernel
      have hl : raw26549step0Labels = raw26549Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26549 raw26549Labels permutation184 permutation5
    mixedMoment B raw26549step0 raw26549step0Labels = mixedMoment B raw26549step1 raw26549step1Labels := by
      have ha : raw26549step1 = -raw26549step0 := by apply Matrix.ext; change ∀ i j, raw26549step1 i j = -(raw26549step0 i j); unfold raw26549step1 raw26549step0; decide +kernel
      have hl : raw26549step1Labels = raw26549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26549step1 raw26549step1Labels = mixedMoment B raw26549step2 raw26549step2Labels := by
      have ha : raw26549step2 = raw26549step1 := by apply Matrix.ext; unfold raw26549step2 raw26549step1; decide +kernel
      have hl : raw26549step1Labels = labelEmbedding1 ∘ raw26549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26549step1 raw26549step1Labels raw26549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw26550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26550step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26550step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26550step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26550 raw26550Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26550 raw26550Labels = mixedMoment B raw26550step0 raw26550step0Labels := by
      have ha : raw26550step0 = (fun i j => raw26550 (permutation208 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26550step0 raw26550; decide +kernel
      have hl : raw26550step0Labels = raw26550Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26550 raw26550Labels permutation208 permutation5
    mixedMoment B raw26550step0 raw26550step0Labels = mixedMoment B raw26550step1 raw26550step1Labels := by
      have ha : raw26550step1 = -raw26550step0 := by apply Matrix.ext; change ∀ i j, raw26550step1 i j = -(raw26550step0 i j); unfold raw26550step1 raw26550step0; decide +kernel
      have hl : raw26550step1Labels = raw26550step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26550step1 raw26550step1Labels = mixedMoment B raw26550step2 raw26550step2Labels := by
      have ha : raw26550step2 = raw26550step1 := by apply Matrix.ext; unfold raw26550step2 raw26550step1; decide +kernel
      have hl : raw26550step1Labels = labelEmbedding1 ∘ raw26550step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26550step1 raw26550step1Labels raw26550step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw26551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26551step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26551step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26551step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26551 raw26551Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26551 raw26551Labels = mixedMoment B raw26551step0 raw26551step0Labels := by
      have ha : raw26551step0 = (fun i j => raw26551 (permutation232 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26551step0 raw26551; decide +kernel
      have hl : raw26551step0Labels = raw26551Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26551 raw26551Labels permutation232 permutation5
    mixedMoment B raw26551step0 raw26551step0Labels = mixedMoment B raw26551step1 raw26551step1Labels := by
      have ha : raw26551step1 = -raw26551step0 := by apply Matrix.ext; change ∀ i j, raw26551step1 i j = -(raw26551step0 i j); unfold raw26551step1 raw26551step0; decide +kernel
      have hl : raw26551step1Labels = raw26551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26551step1 raw26551step1Labels = mixedMoment B raw26551step2 raw26551step2Labels := by
      have ha : raw26551step2 = raw26551step1 := by apply Matrix.ext; unfold raw26551step2 raw26551step1; decide +kernel
      have hl : raw26551step1Labels = labelEmbedding1 ∘ raw26551step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26551step1 raw26551step1Labels raw26551step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw26552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26552step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26552 raw26552Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw26552 raw26552Labels = mixedMoment B raw26552step0 raw26552step0Labels := by
      have ha : raw26552step0 = (fun i j => raw26552 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26552step0 raw26552; decide +kernel
      have hl : raw26552step0Labels = raw26552Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26552 raw26552Labels permutation246 permutation7
    mixedMoment B raw26552step0 raw26552step0Labels = mixedMoment B raw26552step1 raw26552step1Labels := by
      have ha : raw26552step1 = -raw26552step0 := by apply Matrix.ext; change ∀ i j, raw26552step1 i j = -(raw26552step0 i j); unfold raw26552step1 raw26552step0; decide +kernel
      have hl : raw26552step1Labels = raw26552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26552step1 raw26552step1Labels = mixedMoment B raw26552step2 raw26552step2Labels := by
      have ha : raw26552step2 = raw26552step1 := by apply Matrix.ext; unfold raw26552step2 raw26552step1; decide +kernel
      have hl : raw26552step1Labels = labelEmbedding1 ∘ raw26552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26552step1 raw26552step1Labels raw26552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

def raw26553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26553step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26553step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26553step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26553step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26553 raw26553Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw26553 raw26553Labels = mixedMoment B raw26553step0 raw26553step0Labels := by
      have hz : ∀ j, raw26553 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26553step0 = (fun i j => raw26553 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26553step0 raw26553; decide +kernel
      have hl : raw26553step0Labels = raw26553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26553 raw26553Labels permutation265 hz
    mixedMoment B raw26553step0 raw26553step0Labels = mixedMoment B raw26553step1 raw26553step1Labels := by
      have ha : raw26553step1 = (fun i j => raw26553step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26553step1 raw26553step0; decide +kernel
      have hl : raw26553step1Labels = raw26553step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26553step0 raw26553step0Labels permutation40 permutation5
    mixedMoment B raw26553step1 raw26553step1Labels = mixedMoment B raw26553step2 raw26553step2Labels := by
      have ha : raw26553step2 = -raw26553step1 := by apply Matrix.ext; change ∀ i j, raw26553step2 i j = -(raw26553step1 i j); unfold raw26553step2 raw26553step1; decide +kernel
      have hl : raw26553step2Labels = raw26553step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26553step2 raw26553step2Labels = mixedMoment B raw26553step3 raw26553step3Labels := by
      have ha : raw26553step3 = raw26553step2 := by apply Matrix.ext; unfold raw26553step3 raw26553step2; decide +kernel
      have hl : raw26553step2Labels = labelEmbedding1 ∘ raw26553step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26553step2 raw26553step2Labels raw26553step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

def raw26554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26554step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26554step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26554 raw26554Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw26554 raw26554Labels = mixedMoment B raw26554step0 raw26554step0Labels := by
      have ha : raw26554step0 = (fun i j => raw26554 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26554step0 raw26554; decide +kernel
      have hl : raw26554step0Labels = raw26554Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26554 raw26554Labels permutation160 permutation5
    mixedMoment B raw26554step0 raw26554step0Labels = mixedMoment B raw26554step1 raw26554step1Labels := by
      have ha : raw26554step1 = -raw26554step0 := by apply Matrix.ext; change ∀ i j, raw26554step1 i j = -(raw26554step0 i j); unfold raw26554step1 raw26554step0; decide +kernel
      have hl : raw26554step1Labels = raw26554step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26554step1 raw26554step1Labels = mixedMoment B raw26554step2 raw26554step2Labels := by
      have ha : raw26554step2 = raw26554step1 := by apply Matrix.ext; unfold raw26554step2 raw26554step1; decide +kernel
      have hl : raw26554step1Labels = labelEmbedding1 ∘ raw26554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26554step1 raw26554step1Labels raw26554step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

def raw26555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26555step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26555step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26555step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26555step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26555step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26555 raw26555Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26555 raw26555Labels = mixedMoment B raw26555step0 raw26555step0Labels := by
      have hz : ∀ j, raw26555 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26555step0 = (fun i j => raw26555 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26555step0 raw26555; decide +kernel
      have hl : raw26555step0Labels = raw26555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26555 raw26555Labels permutation265 hz
    mixedMoment B raw26555step0 raw26555step0Labels = mixedMoment B raw26555step1 raw26555step1Labels := by
      have ha : raw26555step1 = (fun i j => raw26555step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26555step1 raw26555step0; decide +kernel
      have hl : raw26555step1Labels = raw26555step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26555step0 raw26555step0Labels permutation40 permutation5
    mixedMoment B raw26555step1 raw26555step1Labels = mixedMoment B raw26555step2 raw26555step2Labels := by
      have ha : raw26555step2 = -raw26555step1 := by apply Matrix.ext; change ∀ i j, raw26555step2 i j = -(raw26555step1 i j); unfold raw26555step2 raw26555step1; decide +kernel
      have hl : raw26555step2Labels = raw26555step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26555step2 raw26555step2Labels = mixedMoment B raw26555step3 raw26555step3Labels := by
      have ha : raw26555step3 = raw26555step2 := by apply Matrix.ext; unfold raw26555step3 raw26555step2; decide +kernel
      have hl : raw26555step2Labels = labelEmbedding1 ∘ raw26555step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26555step2 raw26555step2Labels raw26555step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw26556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26556step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26556step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26556step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26556step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26556 raw26556Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26556 raw26556Labels = mixedMoment B raw26556step0 raw26556step0Labels := by
      have hz : ∀ j, raw26556 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26556step0 = (fun i j => raw26556 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26556step0 raw26556; decide +kernel
      have hl : raw26556step0Labels = raw26556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26556 raw26556Labels permutation265 hz
    mixedMoment B raw26556step0 raw26556step0Labels = mixedMoment B raw26556step1 raw26556step1Labels := by
      have ha : raw26556step1 = (fun i j => raw26556step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26556step1 raw26556step0; decide +kernel
      have hl : raw26556step1Labels = raw26556step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26556step0 raw26556step0Labels permutation46 permutation5
    mixedMoment B raw26556step1 raw26556step1Labels = mixedMoment B raw26556step2 raw26556step2Labels := by
      have ha : raw26556step2 = -raw26556step1 := by apply Matrix.ext; change ∀ i j, raw26556step2 i j = -(raw26556step1 i j); unfold raw26556step2 raw26556step1; decide +kernel
      have hl : raw26556step2Labels = raw26556step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26556step2 raw26556step2Labels = mixedMoment B raw26556step3 raw26556step3Labels := by
      have ha : raw26556step3 = raw26556step2 := by apply Matrix.ext; unfold raw26556step3 raw26556step2; decide +kernel
      have hl : raw26556step2Labels = labelEmbedding1 ∘ raw26556step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26556step2 raw26556step2Labels raw26556step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw26557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26557Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26557step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26557step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26557step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26557step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26557step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26557step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26557 raw26557Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26557 raw26557Labels = mixedMoment B raw26557step0 raw26557step0Labels := by
      have hz : ∀ j, raw26557 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26557step0 = (fun i j => raw26557 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26557step0 raw26557; decide +kernel
      have hl : raw26557step0Labels = raw26557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26557 raw26557Labels permutation265 hz
    mixedMoment B raw26557step0 raw26557step0Labels = mixedMoment B raw26557step1 raw26557step1Labels := by
      have ha : raw26557step1 = (fun i j => raw26557step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26557step1 raw26557step0; decide +kernel
      have hl : raw26557step1Labels = raw26557step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26557step0 raw26557step0Labels permutation53 permutation7
    mixedMoment B raw26557step1 raw26557step1Labels = mixedMoment B raw26557step2 raw26557step2Labels := by
      have ha : raw26557step2 = -raw26557step1 := by apply Matrix.ext; change ∀ i j, raw26557step2 i j = -(raw26557step1 i j); unfold raw26557step2 raw26557step1; decide +kernel
      have hl : raw26557step2Labels = raw26557step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26557step2 raw26557step2Labels = mixedMoment B raw26557step3 raw26557step3Labels := by
      have ha : raw26557step3 = raw26557step2 := by apply Matrix.ext; unfold raw26557step3 raw26557step2; decide +kernel
      have hl : raw26557step2Labels = labelEmbedding1 ∘ raw26557step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26557step2 raw26557step2Labels raw26557step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw26558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26558step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26558step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26558step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26558step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26558 raw26558Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw26558 raw26558Labels = mixedMoment B raw26558step0 raw26558step0Labels := by
      have hz : ∀ j, raw26558 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26558step0 = (fun i j => raw26558 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26558step0 raw26558; decide +kernel
      have hl : raw26558step0Labels = raw26558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26558 raw26558Labels permutation265 hz
    mixedMoment B raw26558step0 raw26558step0Labels = mixedMoment B raw26558step1 raw26558step1Labels := by
      have ha : raw26558step1 = (fun i j => raw26558step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26558step1 raw26558step0; decide +kernel
      have hl : raw26558step1Labels = raw26558step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26558step0 raw26558step0Labels permutation34 permutation5
    mixedMoment B raw26558step1 raw26558step1Labels = mixedMoment B raw26558step2 raw26558step2Labels := by
      have ha : raw26558step2 = -raw26558step1 := by apply Matrix.ext; change ∀ i j, raw26558step2 i j = -(raw26558step1 i j); unfold raw26558step2 raw26558step1; decide +kernel
      have hl : raw26558step2Labels = raw26558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26558step2 raw26558step2Labels = mixedMoment B raw26558step3 raw26558step3Labels := by
      have ha : raw26558step3 = raw26558step2 := by apply Matrix.ext; unfold raw26558step3 raw26558step2; decide +kernel
      have hl : raw26558step2Labels = labelEmbedding1 ∘ raw26558step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26558step2 raw26558step2Labels raw26558step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

def raw26559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26559Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26559step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26559step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26559 raw26559Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw26559 raw26559Labels = mixedMoment B raw26559step0 raw26559step0Labels := by
      have ha : raw26559step0 = (fun i j => raw26559 (permutation154 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26559step0 raw26559; decide +kernel
      have hl : raw26559step0Labels = raw26559Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26559 raw26559Labels permutation154 permutation5
    mixedMoment B raw26559step0 raw26559step0Labels = mixedMoment B raw26559step1 raw26559step1Labels := by
      have ha : raw26559step1 = -raw26559step0 := by apply Matrix.ext; change ∀ i j, raw26559step1 i j = -(raw26559step0 i j); unfold raw26559step1 raw26559step0; decide +kernel
      have hl : raw26559step1Labels = raw26559step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26559step1 raw26559step1Labels = mixedMoment B raw26559step2 raw26559step2Labels := by
      have ha : raw26559step2 = raw26559step1 := by apply Matrix.ext; unfold raw26559step2 raw26559step1; decide +kernel
      have hl : raw26559step1Labels = labelEmbedding1 ∘ raw26559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26559step1 raw26559step1Labels raw26559step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

def raw26560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26560step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26560step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26560step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26560step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26560 raw26560Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26560 raw26560Labels = mixedMoment B raw26560step0 raw26560step0Labels := by
      have hz : ∀ j, raw26560 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26560step0 = (fun i j => raw26560 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26560step0 raw26560; decide +kernel
      have hl : raw26560step0Labels = raw26560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26560 raw26560Labels permutation265 hz
    mixedMoment B raw26560step0 raw26560step0Labels = mixedMoment B raw26560step1 raw26560step1Labels := by
      have ha : raw26560step1 = (fun i j => raw26560step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26560step1 raw26560step0; decide +kernel
      have hl : raw26560step1Labels = raw26560step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26560step0 raw26560step0Labels permutation34 permutation5
    mixedMoment B raw26560step1 raw26560step1Labels = mixedMoment B raw26560step2 raw26560step2Labels := by
      have ha : raw26560step2 = -raw26560step1 := by apply Matrix.ext; change ∀ i j, raw26560step2 i j = -(raw26560step1 i j); unfold raw26560step2 raw26560step1; decide +kernel
      have hl : raw26560step2Labels = raw26560step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26560step2 raw26560step2Labels = mixedMoment B raw26560step3 raw26560step3Labels := by
      have ha : raw26560step3 = raw26560step2 := by apply Matrix.ext; unfold raw26560step3 raw26560step2; decide +kernel
      have hl : raw26560step2Labels = labelEmbedding1 ∘ raw26560step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26560step2 raw26560step2Labels raw26560step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw26561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26561Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26561step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26561step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26561step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26561step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26561 raw26561Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26561 raw26561Labels = mixedMoment B raw26561step0 raw26561step0Labels := by
      have hz : ∀ j, raw26561 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26561step0 = (fun i j => raw26561 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26561step0 raw26561; decide +kernel
      have hl : raw26561step0Labels = raw26561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26561 raw26561Labels permutation265 hz
    mixedMoment B raw26561step0 raw26561step0Labels = mixedMoment B raw26561step1 raw26561step1Labels := by
      have ha : raw26561step1 = (fun i j => raw26561step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26561step1 raw26561step0; decide +kernel
      have hl : raw26561step1Labels = raw26561step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26561step0 raw26561step0Labels permutation44 permutation5
    mixedMoment B raw26561step1 raw26561step1Labels = mixedMoment B raw26561step2 raw26561step2Labels := by
      have ha : raw26561step2 = -raw26561step1 := by apply Matrix.ext; change ∀ i j, raw26561step2 i j = -(raw26561step1 i j); unfold raw26561step2 raw26561step1; decide +kernel
      have hl : raw26561step2Labels = raw26561step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26561step2 raw26561step2Labels = mixedMoment B raw26561step3 raw26561step3Labels := by
      have ha : raw26561step3 = raw26561step2 := by apply Matrix.ext; unfold raw26561step3 raw26561step2; decide +kernel
      have hl : raw26561step2Labels = labelEmbedding1 ∘ raw26561step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26561step2 raw26561step2Labels raw26561step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw26562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26562step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26562step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26562step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26562step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26562 raw26562Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26562 raw26562Labels = mixedMoment B raw26562step0 raw26562step0Labels := by
      have hz : ∀ j, raw26562 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26562step0 = (fun i j => raw26562 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26562step0 raw26562; decide +kernel
      have hl : raw26562step0Labels = raw26562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26562 raw26562Labels permutation265 hz
    mixedMoment B raw26562step0 raw26562step0Labels = mixedMoment B raw26562step1 raw26562step1Labels := by
      have ha : raw26562step1 = (fun i j => raw26562step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26562step1 raw26562step0; decide +kernel
      have hl : raw26562step1Labels = raw26562step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26562step0 raw26562step0Labels permutation51 permutation7
    mixedMoment B raw26562step1 raw26562step1Labels = mixedMoment B raw26562step2 raw26562step2Labels := by
      have ha : raw26562step2 = -raw26562step1 := by apply Matrix.ext; change ∀ i j, raw26562step2 i j = -(raw26562step1 i j); unfold raw26562step2 raw26562step1; decide +kernel
      have hl : raw26562step2Labels = raw26562step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26562step2 raw26562step2Labels = mixedMoment B raw26562step3 raw26562step3Labels := by
      have ha : raw26562step3 = raw26562step2 := by apply Matrix.ext; unfold raw26562step3 raw26562step2; decide +kernel
      have hl : raw26562step2Labels = labelEmbedding1 ∘ raw26562step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26562step2 raw26562step2Labels raw26562step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw26563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26563Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26563step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26563step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26563step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26563step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26563step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26563 raw26563Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw26563 raw26563Labels = mixedMoment B raw26563step0 raw26563step0Labels := by
      have hz : ∀ j, raw26563 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26563step0 = (fun i j => raw26563 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26563step0 raw26563; decide +kernel
      have hl : raw26563step0Labels = raw26563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26563 raw26563Labels permutation265 hz
    mixedMoment B raw26563step0 raw26563step0Labels = mixedMoment B raw26563step1 raw26563step1Labels := by
      have ha : raw26563step1 = (fun i j => raw26563step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26563step1 raw26563step0; decide +kernel
      have hl : raw26563step1Labels = raw26563step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26563step0 raw26563step0Labels permutation32 permutation5
    mixedMoment B raw26563step1 raw26563step1Labels = mixedMoment B raw26563step2 raw26563step2Labels := by
      have ha : raw26563step2 = -raw26563step1 := by apply Matrix.ext; change ∀ i j, raw26563step2 i j = -(raw26563step1 i j); unfold raw26563step2 raw26563step1; decide +kernel
      have hl : raw26563step2Labels = raw26563step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26563step2 raw26563step2Labels = mixedMoment B raw26563step3 raw26563step3Labels := by
      have ha : raw26563step3 = raw26563step2 := by apply Matrix.ext; unfold raw26563step3 raw26563step2; decide +kernel
      have hl : raw26563step2Labels = labelEmbedding1 ∘ raw26563step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26563step2 raw26563step2Labels raw26563step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

def raw26564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26564Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26564step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26564step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26564 raw26564Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw26564 raw26564Labels = mixedMoment B raw26564step0 raw26564step0Labels := by
      have ha : raw26564step0 = (fun i j => raw26564 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26564step0 raw26564; decide +kernel
      have hl : raw26564step0Labels = raw26564Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26564 raw26564Labels permutation152 permutation5
    mixedMoment B raw26564step0 raw26564step0Labels = mixedMoment B raw26564step1 raw26564step1Labels := by
      have ha : raw26564step1 = -raw26564step0 := by apply Matrix.ext; change ∀ i j, raw26564step1 i j = -(raw26564step0 i j); unfold raw26564step1 raw26564step0; decide +kernel
      have hl : raw26564step1Labels = raw26564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26564step1 raw26564step1Labels = mixedMoment B raw26564step2 raw26564step2Labels := by
      have ha : raw26564step2 = raw26564step1 := by apply Matrix.ext; unfold raw26564step2 raw26564step1; decide +kernel
      have hl : raw26564step1Labels = labelEmbedding1 ∘ raw26564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26564step1 raw26564step1Labels raw26564step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

def raw26565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26565Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26565step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26565step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26565step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26565step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26565step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26565 raw26565Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26565 raw26565Labels = mixedMoment B raw26565step0 raw26565step0Labels := by
      have hz : ∀ j, raw26565 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26565step0 = (fun i j => raw26565 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26565step0 raw26565; decide +kernel
      have hl : raw26565step0Labels = raw26565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26565 raw26565Labels permutation265 hz
    mixedMoment B raw26565step0 raw26565step0Labels = mixedMoment B raw26565step1 raw26565step1Labels := by
      have ha : raw26565step1 = (fun i j => raw26565step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26565step1 raw26565step0; decide +kernel
      have hl : raw26565step1Labels = raw26565step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26565step0 raw26565step0Labels permutation32 permutation5
    mixedMoment B raw26565step1 raw26565step1Labels = mixedMoment B raw26565step2 raw26565step2Labels := by
      have ha : raw26565step2 = -raw26565step1 := by apply Matrix.ext; change ∀ i j, raw26565step2 i j = -(raw26565step1 i j); unfold raw26565step2 raw26565step1; decide +kernel
      have hl : raw26565step2Labels = raw26565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26565step2 raw26565step2Labels = mixedMoment B raw26565step3 raw26565step3Labels := by
      have ha : raw26565step3 = raw26565step2 := by apply Matrix.ext; unfold raw26565step3 raw26565step2; decide +kernel
      have hl : raw26565step2Labels = labelEmbedding1 ∘ raw26565step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26565step2 raw26565step2Labels raw26565step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw26566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26566Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26566step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26566step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26566step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26566 raw26566Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26566 raw26566Labels = mixedMoment B raw26566step0 raw26566step0Labels := by
      have hz : ∀ j, raw26566 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26566step0 = (fun i j => raw26566 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26566step0 raw26566; decide +kernel
      have hl : raw26566step0Labels = raw26566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26566 raw26566Labels permutation265 hz
    mixedMoment B raw26566step0 raw26566step0Labels = mixedMoment B raw26566step1 raw26566step1Labels := by
      have ha : raw26566step1 = (fun i j => raw26566step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26566step1 raw26566step0; decide +kernel
      have hl : raw26566step1Labels = raw26566step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26566step0 raw26566step0Labels permutation38 permutation5
    mixedMoment B raw26566step1 raw26566step1Labels = mixedMoment B raw26566step2 raw26566step2Labels := by
      have ha : raw26566step2 = -raw26566step1 := by apply Matrix.ext; change ∀ i j, raw26566step2 i j = -(raw26566step1 i j); unfold raw26566step2 raw26566step1; decide +kernel
      have hl : raw26566step2Labels = raw26566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26566step2 raw26566step2Labels = mixedMoment B raw26566step3 raw26566step3Labels := by
      have ha : raw26566step3 = raw26566step2 := by apply Matrix.ext; unfold raw26566step3 raw26566step2; decide +kernel
      have hl : raw26566step2Labels = labelEmbedding1 ∘ raw26566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26566step2 raw26566step2Labels raw26566step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw26567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26567Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26567step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26567step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26567step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26567step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26567step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26567 raw26567Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26567 raw26567Labels = mixedMoment B raw26567step0 raw26567step0Labels := by
      have hz : ∀ j, raw26567 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26567step0 = (fun i j => raw26567 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26567step0 raw26567; decide +kernel
      have hl : raw26567step0Labels = raw26567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26567 raw26567Labels permutation265 hz
    mixedMoment B raw26567step0 raw26567step0Labels = mixedMoment B raw26567step1 raw26567step1Labels := by
      have ha : raw26567step1 = (fun i j => raw26567step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26567step1 raw26567step0; decide +kernel
      have hl : raw26567step1Labels = raw26567step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26567step0 raw26567step0Labels permutation50 permutation7
    mixedMoment B raw26567step1 raw26567step1Labels = mixedMoment B raw26567step2 raw26567step2Labels := by
      have ha : raw26567step2 = -raw26567step1 := by apply Matrix.ext; change ∀ i j, raw26567step2 i j = -(raw26567step1 i j); unfold raw26567step2 raw26567step1; decide +kernel
      have hl : raw26567step2Labels = raw26567step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26567step2 raw26567step2Labels = mixedMoment B raw26567step3 raw26567step3Labels := by
      have ha : raw26567step3 = raw26567step2 := by apply Matrix.ext; unfold raw26567step3 raw26567step2; decide +kernel
      have hl : raw26567step2Labels = labelEmbedding1 ∘ raw26567step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26567step2 raw26567step2Labels raw26567step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw26568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26568Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26568step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw26568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw26568step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26568step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw26568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26568 raw26568Labels = mixedMoment B node1503 node1503Labels := by
  calc
    mixedMoment B raw26568 raw26568Labels = mixedMoment B raw26568step0 raw26568step0Labels := by
      have hz : ∀ j, raw26568 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26568step0 = (fun i j => raw26568 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26568step0 raw26568; decide +kernel
      have hl : raw26568step0Labels = raw26568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26568 raw26568Labels permutation265 hz
    mixedMoment B raw26568step0 raw26568step0Labels = mixedMoment B raw26568step1 raw26568step1Labels := by
      have ha : raw26568step1 = (fun i j => raw26568step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26568step1 raw26568step0; decide +kernel
      have hl : raw26568step1Labels = raw26568step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26568step0 raw26568step0Labels permutation32 permutation5
    mixedMoment B raw26568step1 raw26568step1Labels = mixedMoment B raw26568step2 raw26568step2Labels := by
      have ha : raw26568step2 = -raw26568step1 := by apply Matrix.ext; change ∀ i j, raw26568step2 i j = -(raw26568step1 i j); unfold raw26568step2 raw26568step1; decide +kernel
      have hl : raw26568step2Labels = raw26568step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26568step2 raw26568step2Labels = mixedMoment B raw26568step3 raw26568step3Labels := by
      have ha : raw26568step3 = raw26568step2 := by apply Matrix.ext; unfold raw26568step3 raw26568step2; decide +kernel
      have hl : raw26568step2Labels = labelEmbedding1 ∘ raw26568step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26568step2 raw26568step2Labels raw26568step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1503 node1503Labels := by rfl

def raw26569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26569Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw26569step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw26569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26569 raw26569Labels = mixedMoment B node2688 node2688Labels := by
  calc
    mixedMoment B raw26569 raw26569Labels = mixedMoment B raw26569step0 raw26569step0Labels := by
      have ha : raw26569step0 = (fun i j => raw26569 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26569step0 raw26569; decide +kernel
      have hl : raw26569step0Labels = raw26569Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26569 raw26569Labels permutation640 permutation5
    mixedMoment B raw26569step0 raw26569step0Labels = mixedMoment B raw26569step1 raw26569step1Labels := by
      have ha : raw26569step1 = raw26569step0 := by apply Matrix.ext; unfold raw26569step1 raw26569step0; decide +kernel
      have hl : raw26569step0Labels = labelEmbedding1 ∘ raw26569step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26569step0 raw26569step0Labels raw26569step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2688 node2688Labels := by rfl

def raw26570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26570Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26570step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw26570step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw26570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26570 raw26570Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw26570 raw26570Labels = mixedMoment B raw26570step0 raw26570step0Labels := by
      have hz : ∀ j, raw26570 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26570step0 = (fun i j => raw26570 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26570step0 raw26570; decide +kernel
      have hl : raw26570step0Labels = raw26570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26570 raw26570Labels permutation265 hz
    mixedMoment B raw26570step0 raw26570step0Labels = mixedMoment B raw26570step1 raw26570step1Labels := by
      have ha : raw26570step1 = (fun i j => raw26570step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26570step1 raw26570step0; decide +kernel
      have hl : raw26570step1Labels = raw26570step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26570step0 raw26570step0Labels permutation137 permutation5
    mixedMoment B raw26570step1 raw26570step1Labels = mixedMoment B raw26570step2 raw26570step2Labels := by
      have ha : raw26570step2 = raw26570step1 := by apply Matrix.ext; unfold raw26570step2 raw26570step1; decide +kernel
      have hl : raw26570step1Labels = labelEmbedding1 ∘ raw26570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26570step1 raw26570step1Labels raw26570step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw26571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26571 raw26571Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw26571 raw26571Labels = mixedMoment B raw26571step0 raw26571step0Labels := by
      have hz : ∀ j, raw26571 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26571step0 = (fun i j => raw26571 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26571step0 raw26571; decide +kernel
      have hl : raw26571step0Labels = raw26571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26571 raw26571Labels permutation265 hz
    mixedMoment B raw26571step0 raw26571step0Labels = mixedMoment B raw26571step1 raw26571step1Labels := by
      have ha : raw26571step1 = (fun i j => raw26571step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26571step1 raw26571step0; decide +kernel
      have hl : raw26571step1Labels = raw26571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26571step0 raw26571step0Labels permutation50 permutation2
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw26572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26572 raw26572Labels = mixedMoment B node637 node637Labels := by
  calc
    mixedMoment B raw26572 raw26572Labels = mixedMoment B raw26572step0 raw26572step0Labels := by
      have ha : raw26572step0 = (fun i j => raw26572 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26572step0 raw26572; decide +kernel
      have hl : raw26572step0Labels = raw26572Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26572 raw26572Labels permutation246 permutation2
    _ = mixedMoment B node637 node637Labels := by rfl

def raw26573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26573 raw26573Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw26573 raw26573Labels = mixedMoment B raw26573step0 raw26573step0Labels := by
      have hz : ∀ j, raw26573 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26573step0 = (fun i j => raw26573 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26573step0 raw26573; decide +kernel
      have hl : raw26573step0Labels = raw26573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26573 raw26573Labels permutation265 hz
    mixedMoment B raw26573step0 raw26573step0Labels = mixedMoment B raw26573step1 raw26573step1Labels := by
      have ha : raw26573step1 = (fun i j => raw26573step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26573step1 raw26573step0; decide +kernel
      have hl : raw26573step1Labels = raw26573step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26573step0 raw26573step0Labels permutation53 permutation2
    _ = mixedMoment B node640 node640Labels := by rfl

def raw26574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26574 raw26574Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw26574 raw26574Labels = mixedMoment B raw26574step0 raw26574step0Labels := by
      have hz : ∀ j, raw26574 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26574step0 = (fun i j => raw26574 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26574step0 raw26574; decide +kernel
      have hl : raw26574step0Labels = raw26574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26574 raw26574Labels permutation265 hz
    mixedMoment B raw26574step0 raw26574step0Labels = mixedMoment B raw26574step1 raw26574step1Labels := by
      have ha : raw26574step1 = (fun i j => raw26574step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26574step1 raw26574step0; decide +kernel
      have hl : raw26574step1Labels = raw26574step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26574step0 raw26574step0Labels permutation51 permutation2
    _ = mixedMoment B node640 node640Labels := by rfl

def raw26575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26575 raw26575Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw26575 raw26575Labels = mixedMoment B raw26575step0 raw26575step0Labels := by
      have hz : ∀ j, raw26575 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26575step0 = (fun i j => raw26575 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26575step0 raw26575; decide +kernel
      have hl : raw26575step0Labels = raw26575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26575 raw26575Labels permutation265 hz
    mixedMoment B raw26575step0 raw26575step0Labels = mixedMoment B raw26575step1 raw26575step1Labels := by
      have ha : raw26575step1 = (fun i j => raw26575step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26575step1 raw26575step0; decide +kernel
      have hl : raw26575step1Labels = raw26575step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26575step0 raw26575step0Labels permutation50 permutation2
    _ = mixedMoment B node640 node640Labels := by rfl

def raw26576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26576 raw26576Labels = mixedMoment B node651 node651Labels := by
  calc
    mixedMoment B raw26576 raw26576Labels = mixedMoment B raw26576step0 raw26576step0Labels := by
      have hz : ∀ j, raw26576 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26576step0 = (fun i j => raw26576 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26576step0 raw26576; decide +kernel
      have hl : raw26576step0Labels = raw26576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26576 raw26576Labels permutation265 hz
    _ = mixedMoment B node651 node651Labels := by rfl

def raw26577 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26577step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26577 raw26577Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw26577 raw26577Labels = mixedMoment B raw26577step0 raw26577step0Labels := by
      have ha : raw26577step0 = (fun i j => raw26577 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26577step0 raw26577; decide +kernel
      have hl : raw26577step0Labels = raw26577Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26577 raw26577Labels permutation170 permutation7
    mixedMoment B raw26577step0 raw26577step0Labels = mixedMoment B raw26577step1 raw26577step1Labels := by
      have ha : raw26577step1 = raw26577step0 := by apply Matrix.ext; unfold raw26577step1 raw26577step0; decide +kernel
      have hl : raw26577step0Labels = labelEmbedding10 ∘ raw26577step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26577step0 raw26577step0Labels raw26577step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw26578 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26578step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26578 raw26578Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw26578 raw26578Labels = mixedMoment B raw26578step0 raw26578step0Labels := by
      have hz : ∀ j, raw26578 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26578step0 = (fun i j => raw26578 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26578step0 raw26578; decide +kernel
      have hl : raw26578step0Labels = raw26578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26578 raw26578Labels permutation265 hz
    mixedMoment B raw26578step0 raw26578step0Labels = mixedMoment B raw26578step1 raw26578step1Labels := by
      have ha : raw26578step1 = (fun i j => raw26578step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26578step1 raw26578step0; decide +kernel
      have hl : raw26578step1Labels = raw26578step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26578step0 raw26578step0Labels permutation53 permutation7
    mixedMoment B raw26578step1 raw26578step1Labels = mixedMoment B raw26578step2 raw26578step2Labels := by
      have ha : raw26578step2 = raw26578step1 := by apply Matrix.ext; unfold raw26578step2 raw26578step1; decide +kernel
      have hl : raw26578step1Labels = labelEmbedding10 ∘ raw26578step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26578step1 raw26578step1Labels raw26578step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw26579 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26579step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26579step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26579step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26579 raw26579Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw26579 raw26579Labels = mixedMoment B raw26579step0 raw26579step0Labels := by
      have hz : ∀ j, raw26579 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26579step0 = (fun i j => raw26579 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26579step0 raw26579; decide +kernel
      have hl : raw26579step0Labels = raw26579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26579 raw26579Labels permutation265 hz
    mixedMoment B raw26579step0 raw26579step0Labels = mixedMoment B raw26579step1 raw26579step1Labels := by
      have ha : raw26579step1 = (fun i j => raw26579step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26579step1 raw26579step0; decide +kernel
      have hl : raw26579step1Labels = raw26579step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26579step0 raw26579step0Labels permutation51 permutation7
    mixedMoment B raw26579step1 raw26579step1Labels = mixedMoment B raw26579step2 raw26579step2Labels := by
      have ha : raw26579step2 = raw26579step1 := by apply Matrix.ext; unfold raw26579step2 raw26579step1; decide +kernel
      have hl : raw26579step1Labels = labelEmbedding10 ∘ raw26579step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26579step1 raw26579step1Labels raw26579step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw26580 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26580step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26580 raw26580Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw26580 raw26580Labels = mixedMoment B raw26580step0 raw26580step0Labels := by
      have hz : ∀ j, raw26580 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26580step0 = (fun i j => raw26580 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26580step0 raw26580; decide +kernel
      have hl : raw26580step0Labels = raw26580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26580 raw26580Labels permutation265 hz
    mixedMoment B raw26580step0 raw26580step0Labels = mixedMoment B raw26580step1 raw26580step1Labels := by
      have ha : raw26580step1 = (fun i j => raw26580step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26580step1 raw26580step0; decide +kernel
      have hl : raw26580step1Labels = raw26580step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26580step0 raw26580step0Labels permutation50 permutation7
    mixedMoment B raw26580step1 raw26580step1Labels = mixedMoment B raw26580step2 raw26580step2Labels := by
      have ha : raw26580step2 = raw26580step1 := by apply Matrix.ext; unfold raw26580step2 raw26580step1; decide +kernel
      have hl : raw26580step1Labels = labelEmbedding10 ∘ raw26580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26580step1 raw26580step1Labels raw26580step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw26581 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26581step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26581 raw26581Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26581 raw26581Labels = mixedMoment B raw26581step0 raw26581step0Labels := by
      have hz : ∀ j, raw26581 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26581step0 = (fun i j => raw26581 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26581step0 raw26581; decide +kernel
      have hl : raw26581step0Labels = raw26581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26581 raw26581Labels permutation265 hz
    mixedMoment B raw26581step0 raw26581step0Labels = mixedMoment B raw26581step1 raw26581step1Labels := by
      have ha : raw26581step1 = (fun i j => raw26581step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26581step1 raw26581step0; decide +kernel
      have hl : raw26581step1Labels = raw26581step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26581step0 raw26581step0Labels permutation50 permutation7
    mixedMoment B raw26581step1 raw26581step1Labels = mixedMoment B raw26581step2 raw26581step2Labels := by
      have ha : raw26581step2 = raw26581step1 := by apply Matrix.ext; unfold raw26581step2 raw26581step1; decide +kernel
      have hl : raw26581step1Labels = labelEmbedding10 ∘ raw26581step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26581step1 raw26581step1Labels raw26581step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw26582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26582step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26582 raw26582Labels = mixedMoment B node4455 node4455Labels := by
  calc
    mixedMoment B raw26582 raw26582Labels = mixedMoment B raw26582step0 raw26582step0Labels := by
      have ha : raw26582step0 = (fun i j => raw26582 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26582step0 raw26582; decide +kernel
      have hl : raw26582step0Labels = raw26582Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26582 raw26582Labels permutation152 permutation6
    mixedMoment B raw26582step0 raw26582step0Labels = mixedMoment B raw26582step1 raw26582step1Labels := by
      have ha : raw26582step1 = raw26582step0 := by apply Matrix.ext; unfold raw26582step1 raw26582step0; decide +kernel
      have hl : raw26582step0Labels = labelEmbedding9 ∘ raw26582step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26582step0 raw26582step0Labels raw26582step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4455 node4455Labels := by rfl

def raw26583 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26583step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26583 raw26583Labels = mixedMoment B node4595 node4595Labels := by
  calc
    mixedMoment B raw26583 raw26583Labels = mixedMoment B raw26583step0 raw26583step0Labels := by
      have ha : raw26583step0 = (fun i j => raw26583 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26583step0 raw26583; decide +kernel
      have hl : raw26583step0Labels = raw26583Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26583 raw26583Labels permutation173 permutation7
    mixedMoment B raw26583step0 raw26583step0Labels = mixedMoment B raw26583step1 raw26583step1Labels := by
      have ha : raw26583step1 = raw26583step0 := by apply Matrix.ext; unfold raw26583step1 raw26583step0; decide +kernel
      have hl : raw26583step0Labels = labelEmbedding10 ∘ raw26583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26583step0 raw26583step0Labels raw26583step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4595 node4595Labels := by rfl

def raw26584 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26584step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26584 raw26584Labels = mixedMoment B node4595 node4595Labels := by
  calc
    mixedMoment B raw26584 raw26584Labels = mixedMoment B raw26584step0 raw26584step0Labels := by
      have ha : raw26584step0 = (fun i j => raw26584 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26584step0 raw26584; decide +kernel
      have hl : raw26584step0Labels = raw26584Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26584 raw26584Labels permutation171 permutation7
    mixedMoment B raw26584step0 raw26584step0Labels = mixedMoment B raw26584step1 raw26584step1Labels := by
      have ha : raw26584step1 = raw26584step0 := by apply Matrix.ext; unfold raw26584step1 raw26584step0; decide +kernel
      have hl : raw26584step0Labels = labelEmbedding10 ∘ raw26584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26584step0 raw26584step0Labels raw26584step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4595 node4595Labels := by rfl

def raw26585 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26585step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26585step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26585 raw26585Labels = mixedMoment B node4595 node4595Labels := by
  calc
    mixedMoment B raw26585 raw26585Labels = mixedMoment B raw26585step0 raw26585step0Labels := by
      have ha : raw26585step0 = (fun i j => raw26585 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26585step0 raw26585; decide +kernel
      have hl : raw26585step0Labels = raw26585Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26585 raw26585Labels permutation170 permutation7
    mixedMoment B raw26585step0 raw26585step0Labels = mixedMoment B raw26585step1 raw26585step1Labels := by
      have ha : raw26585step1 = raw26585step0 := by apply Matrix.ext; unfold raw26585step1 raw26585step0; decide +kernel
      have hl : raw26585step0Labels = labelEmbedding10 ∘ raw26585step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26585step0 raw26585step0Labels raw26585step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4595 node4595Labels := by rfl

def raw26586 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26586step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26586 raw26586Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26586 raw26586Labels = mixedMoment B raw26586step0 raw26586step0Labels := by
      have ha : raw26586step0 = (fun i j => raw26586 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26586step0 raw26586; decide +kernel
      have hl : raw26586step0Labels = raw26586Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26586 raw26586Labels permutation170 permutation7
    mixedMoment B raw26586step0 raw26586step0Labels = mixedMoment B raw26586step1 raw26586step1Labels := by
      have ha : raw26586step1 = raw26586step0 := by apply Matrix.ext; unfold raw26586step1 raw26586step0; decide +kernel
      have hl : raw26586step0Labels = labelEmbedding10 ∘ raw26586step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26586step0 raw26586step0Labels raw26586step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw26587 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26587step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26587step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26587 raw26587Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26587 raw26587Labels = mixedMoment B raw26587step0 raw26587step0Labels := by
      have hz : ∀ j, raw26587 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26587step0 = (fun i j => raw26587 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26587step0 raw26587; decide +kernel
      have hl : raw26587step0Labels = raw26587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26587 raw26587Labels permutation265 hz
    mixedMoment B raw26587step0 raw26587step0Labels = mixedMoment B raw26587step1 raw26587step1Labels := by
      have ha : raw26587step1 = (fun i j => raw26587step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26587step1 raw26587step0; decide +kernel
      have hl : raw26587step1Labels = raw26587step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26587step0 raw26587step0Labels permutation40 permutation6
    mixedMoment B raw26587step1 raw26587step1Labels = mixedMoment B raw26587step2 raw26587step2Labels := by
      have ha : raw26587step2 = raw26587step1 := by apply Matrix.ext; unfold raw26587step2 raw26587step1; decide +kernel
      have hl : raw26587step1Labels = labelEmbedding9 ∘ raw26587step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26587step1 raw26587step1Labels raw26587step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw26588 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26588step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26588 raw26588Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26588 raw26588Labels = mixedMoment B raw26588step0 raw26588step0Labels := by
      have ha : raw26588step0 = (fun i j => raw26588 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26588step0 raw26588; decide +kernel
      have hl : raw26588step0Labels = raw26588Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26588 raw26588Labels permutation160 permutation6
    mixedMoment B raw26588step0 raw26588step0Labels = mixedMoment B raw26588step1 raw26588step1Labels := by
      have ha : raw26588step1 = raw26588step0 := by apply Matrix.ext; unfold raw26588step1 raw26588step0; decide +kernel
      have hl : raw26588step0Labels = labelEmbedding9 ∘ raw26588step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26588step0 raw26588step0Labels raw26588step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26589 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26589step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26589step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26589 raw26589Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26589 raw26589Labels = mixedMoment B raw26589step0 raw26589step0Labels := by
      have hz : ∀ j, raw26589 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26589step0 = (fun i j => raw26589 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26589step0 raw26589; decide +kernel
      have hl : raw26589step0Labels = raw26589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26589 raw26589Labels permutation265 hz
    mixedMoment B raw26589step0 raw26589step0Labels = mixedMoment B raw26589step1 raw26589step1Labels := by
      have ha : raw26589step1 = (fun i j => raw26589step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26589step1 raw26589step0; decide +kernel
      have hl : raw26589step1Labels = raw26589step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26589step0 raw26589step0Labels permutation40 permutation6
    mixedMoment B raw26589step1 raw26589step1Labels = mixedMoment B raw26589step2 raw26589step2Labels := by
      have ha : raw26589step2 = raw26589step1 := by apply Matrix.ext; unfold raw26589step2 raw26589step1; decide +kernel
      have hl : raw26589step1Labels = labelEmbedding9 ∘ raw26589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26589step1 raw26589step1Labels raw26589step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw26590 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26590step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26590 raw26590Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26590 raw26590Labels = mixedMoment B raw26590step0 raw26590step0Labels := by
      have hz : ∀ j, raw26590 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26590step0 = (fun i j => raw26590 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26590step0 raw26590; decide +kernel
      have hl : raw26590step0Labels = raw26590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26590 raw26590Labels permutation265 hz
    mixedMoment B raw26590step0 raw26590step0Labels = mixedMoment B raw26590step1 raw26590step1Labels := by
      have ha : raw26590step1 = (fun i j => raw26590step0 (permutation46 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26590step1 raw26590step0; decide +kernel
      have hl : raw26590step1Labels = raw26590step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26590step0 raw26590step0Labels permutation46 permutation6
    mixedMoment B raw26590step1 raw26590step1Labels = mixedMoment B raw26590step2 raw26590step2Labels := by
      have ha : raw26590step2 = raw26590step1 := by apply Matrix.ext; unfold raw26590step2 raw26590step1; decide +kernel
      have hl : raw26590step1Labels = labelEmbedding9 ∘ raw26590step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26590step1 raw26590step1Labels raw26590step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw26591 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26591step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26591 raw26591Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26591 raw26591Labels = mixedMoment B raw26591step0 raw26591step0Labels := by
      have hz : ∀ j, raw26591 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26591step0 = (fun i j => raw26591 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26591step0 raw26591; decide +kernel
      have hl : raw26591step0Labels = raw26591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26591 raw26591Labels permutation265 hz
    mixedMoment B raw26591step0 raw26591step0Labels = mixedMoment B raw26591step1 raw26591step1Labels := by
      have ha : raw26591step1 = (fun i j => raw26591step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26591step1 raw26591step0; decide +kernel
      have hl : raw26591step1Labels = raw26591step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26591step0 raw26591step0Labels permutation40 permutation6
    mixedMoment B raw26591step1 raw26591step1Labels = mixedMoment B raw26591step2 raw26591step2Labels := by
      have ha : raw26591step2 = raw26591step1 := by apply Matrix.ext; unfold raw26591step2 raw26591step1; decide +kernel
      have hl : raw26591step1Labels = labelEmbedding9 ∘ raw26591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26591step1 raw26591step1Labels raw26591step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw26592 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26592step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26592step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26592 raw26592Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26592 raw26592Labels = mixedMoment B raw26592step0 raw26592step0Labels := by
      have hz : ∀ j, raw26592 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26592step0 = (fun i j => raw26592 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26592step0 raw26592; decide +kernel
      have hl : raw26592step0Labels = raw26592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26592 raw26592Labels permutation265 hz
    mixedMoment B raw26592step0 raw26592step0Labels = mixedMoment B raw26592step1 raw26592step1Labels := by
      have ha : raw26592step1 = (fun i j => raw26592step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26592step1 raw26592step0; decide +kernel
      have hl : raw26592step1Labels = raw26592step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26592step0 raw26592step0Labels permutation34 permutation6
    mixedMoment B raw26592step1 raw26592step1Labels = mixedMoment B raw26592step2 raw26592step2Labels := by
      have ha : raw26592step2 = raw26592step1 := by apply Matrix.ext; unfold raw26592step2 raw26592step1; decide +kernel
      have hl : raw26592step1Labels = labelEmbedding9 ∘ raw26592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26592step1 raw26592step1Labels raw26592step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw26593 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26593step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26593 raw26593Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26593 raw26593Labels = mixedMoment B raw26593step0 raw26593step0Labels := by
      have ha : raw26593step0 = (fun i j => raw26593 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26593step0 raw26593; decide +kernel
      have hl : raw26593step0Labels = raw26593Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26593 raw26593Labels permutation154 permutation6
    mixedMoment B raw26593step0 raw26593step0Labels = mixedMoment B raw26593step1 raw26593step1Labels := by
      have ha : raw26593step1 = raw26593step0 := by apply Matrix.ext; unfold raw26593step1 raw26593step0; decide +kernel
      have hl : raw26593step0Labels = labelEmbedding9 ∘ raw26593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26593step0 raw26593step0Labels raw26593step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26594 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26594step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26594step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26594 raw26594Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26594 raw26594Labels = mixedMoment B raw26594step0 raw26594step0Labels := by
      have hz : ∀ j, raw26594 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26594step0 = (fun i j => raw26594 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26594step0 raw26594; decide +kernel
      have hl : raw26594step0Labels = raw26594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26594 raw26594Labels permutation265 hz
    mixedMoment B raw26594step0 raw26594step0Labels = mixedMoment B raw26594step1 raw26594step1Labels := by
      have ha : raw26594step1 = (fun i j => raw26594step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26594step1 raw26594step0; decide +kernel
      have hl : raw26594step1Labels = raw26594step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26594step0 raw26594step0Labels permutation34 permutation6
    mixedMoment B raw26594step1 raw26594step1Labels = mixedMoment B raw26594step2 raw26594step2Labels := by
      have ha : raw26594step2 = raw26594step1 := by apply Matrix.ext; unfold raw26594step2 raw26594step1; decide +kernel
      have hl : raw26594step1Labels = labelEmbedding9 ∘ raw26594step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26594step1 raw26594step1Labels raw26594step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw26595 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26595step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26595 raw26595Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26595 raw26595Labels = mixedMoment B raw26595step0 raw26595step0Labels := by
      have hz : ∀ j, raw26595 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26595step0 = (fun i j => raw26595 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26595step0 raw26595; decide +kernel
      have hl : raw26595step0Labels = raw26595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26595 raw26595Labels permutation265 hz
    mixedMoment B raw26595step0 raw26595step0Labels = mixedMoment B raw26595step1 raw26595step1Labels := by
      have ha : raw26595step1 = (fun i j => raw26595step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26595step1 raw26595step0; decide +kernel
      have hl : raw26595step1Labels = raw26595step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26595step0 raw26595step0Labels permutation44 permutation6
    mixedMoment B raw26595step1 raw26595step1Labels = mixedMoment B raw26595step2 raw26595step2Labels := by
      have ha : raw26595step2 = raw26595step1 := by apply Matrix.ext; unfold raw26595step2 raw26595step1; decide +kernel
      have hl : raw26595step1Labels = labelEmbedding9 ∘ raw26595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26595step1 raw26595step1Labels raw26595step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw26596 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26596step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26596 raw26596Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26596 raw26596Labels = mixedMoment B raw26596step0 raw26596step0Labels := by
      have hz : ∀ j, raw26596 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26596step0 = (fun i j => raw26596 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26596step0 raw26596; decide +kernel
      have hl : raw26596step0Labels = raw26596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26596 raw26596Labels permutation265 hz
    mixedMoment B raw26596step0 raw26596step0Labels = mixedMoment B raw26596step1 raw26596step1Labels := by
      have ha : raw26596step1 = (fun i j => raw26596step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26596step1 raw26596step0; decide +kernel
      have hl : raw26596step1Labels = raw26596step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26596step0 raw26596step0Labels permutation34 permutation6
    mixedMoment B raw26596step1 raw26596step1Labels = mixedMoment B raw26596step2 raw26596step2Labels := by
      have ha : raw26596step2 = raw26596step1 := by apply Matrix.ext; unfold raw26596step2 raw26596step1; decide +kernel
      have hl : raw26596step1Labels = labelEmbedding9 ∘ raw26596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26596step1 raw26596step1Labels raw26596step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw26597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26597step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26597step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26597 raw26597Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26597 raw26597Labels = mixedMoment B raw26597step0 raw26597step0Labels := by
      have hz : ∀ j, raw26597 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26597step0 = (fun i j => raw26597 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26597step0 raw26597; decide +kernel
      have hl : raw26597step0Labels = raw26597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26597 raw26597Labels permutation265 hz
    mixedMoment B raw26597step0 raw26597step0Labels = mixedMoment B raw26597step1 raw26597step1Labels := by
      have ha : raw26597step1 = (fun i j => raw26597step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26597step1 raw26597step0; decide +kernel
      have hl : raw26597step1Labels = raw26597step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26597step0 raw26597step0Labels permutation32 permutation6
    mixedMoment B raw26597step1 raw26597step1Labels = mixedMoment B raw26597step2 raw26597step2Labels := by
      have ha : raw26597step2 = raw26597step1 := by apply Matrix.ext; unfold raw26597step2 raw26597step1; decide +kernel
      have hl : raw26597step1Labels = labelEmbedding9 ∘ raw26597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26597step1 raw26597step1Labels raw26597step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw26598 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26598step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26598 raw26598Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26598 raw26598Labels = mixedMoment B raw26598step0 raw26598step0Labels := by
      have ha : raw26598step0 = (fun i j => raw26598 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26598step0 raw26598; decide +kernel
      have hl : raw26598step0Labels = raw26598Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26598 raw26598Labels permutation152 permutation6
    mixedMoment B raw26598step0 raw26598step0Labels = mixedMoment B raw26598step1 raw26598step1Labels := by
      have ha : raw26598step1 = raw26598step0 := by apply Matrix.ext; unfold raw26598step1 raw26598step0; decide +kernel
      have hl : raw26598step0Labels = labelEmbedding9 ∘ raw26598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26598step0 raw26598step0Labels raw26598step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26599 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26599step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26599 raw26599Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26599 raw26599Labels = mixedMoment B raw26599step0 raw26599step0Labels := by
      have hz : ∀ j, raw26599 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26599step0 = (fun i j => raw26599 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26599step0 raw26599; decide +kernel
      have hl : raw26599step0Labels = raw26599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26599 raw26599Labels permutation265 hz
    mixedMoment B raw26599step0 raw26599step0Labels = mixedMoment B raw26599step1 raw26599step1Labels := by
      have ha : raw26599step1 = (fun i j => raw26599step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26599step1 raw26599step0; decide +kernel
      have hl : raw26599step1Labels = raw26599step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26599step0 raw26599step0Labels permutation32 permutation6
    mixedMoment B raw26599step1 raw26599step1Labels = mixedMoment B raw26599step2 raw26599step2Labels := by
      have ha : raw26599step2 = raw26599step1 := by apply Matrix.ext; unfold raw26599step2 raw26599step1; decide +kernel
      have hl : raw26599step1Labels = labelEmbedding9 ∘ raw26599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26599step1 raw26599step1Labels raw26599step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw26600 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26600step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26600 raw26600Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26600 raw26600Labels = mixedMoment B raw26600step0 raw26600step0Labels := by
      have hz : ∀ j, raw26600 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26600step0 = (fun i j => raw26600 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26600step0 raw26600; decide +kernel
      have hl : raw26600step0Labels = raw26600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26600 raw26600Labels permutation265 hz
    mixedMoment B raw26600step0 raw26600step0Labels = mixedMoment B raw26600step1 raw26600step1Labels := by
      have ha : raw26600step1 = (fun i j => raw26600step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26600step1 raw26600step0; decide +kernel
      have hl : raw26600step1Labels = raw26600step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26600step0 raw26600step0Labels permutation38 permutation6
    mixedMoment B raw26600step1 raw26600step1Labels = mixedMoment B raw26600step2 raw26600step2Labels := by
      have ha : raw26600step2 = raw26600step1 := by apply Matrix.ext; unfold raw26600step2 raw26600step1; decide +kernel
      have hl : raw26600step1Labels = labelEmbedding9 ∘ raw26600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26600step1 raw26600step1Labels raw26600step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw26601 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26601step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26601 raw26601Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26601 raw26601Labels = mixedMoment B raw26601step0 raw26601step0Labels := by
      have hz : ∀ j, raw26601 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26601step0 = (fun i j => raw26601 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26601step0 raw26601; decide +kernel
      have hl : raw26601step0Labels = raw26601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26601 raw26601Labels permutation265 hz
    mixedMoment B raw26601step0 raw26601step0Labels = mixedMoment B raw26601step1 raw26601step1Labels := by
      have ha : raw26601step1 = (fun i j => raw26601step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26601step1 raw26601step0; decide +kernel
      have hl : raw26601step1Labels = raw26601step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26601step0 raw26601step0Labels permutation32 permutation6
    mixedMoment B raw26601step1 raw26601step1Labels = mixedMoment B raw26601step2 raw26601step2Labels := by
      have ha : raw26601step2 = raw26601step1 := by apply Matrix.ext; unfold raw26601step2 raw26601step1; decide +kernel
      have hl : raw26601step1Labels = labelEmbedding9 ∘ raw26601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26601step1 raw26601step1Labels raw26601step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw26602 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw26602step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw26602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26602 raw26602Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw26602 raw26602Labels = mixedMoment B raw26602step0 raw26602step0Labels := by
      have hz : ∀ j, raw26602 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26602step0 = (fun i j => raw26602 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26602step0 raw26602; decide +kernel
      have hl : raw26602step0Labels = raw26602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26602 raw26602Labels permutation265 hz
    mixedMoment B raw26602step0 raw26602step0Labels = mixedMoment B raw26602step1 raw26602step1Labels := by
      have ha : raw26602step1 = (fun i j => raw26602step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26602step1 raw26602step0; decide +kernel
      have hl : raw26602step1Labels = raw26602step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26602step0 raw26602step0Labels permutation32 permutation6
    mixedMoment B raw26602step1 raw26602step1Labels = mixedMoment B raw26602step2 raw26602step2Labels := by
      have ha : raw26602step2 = raw26602step1 := by apply Matrix.ext; unfold raw26602step2 raw26602step1; decide +kernel
      have hl : raw26602step1Labels = labelEmbedding9 ∘ raw26602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26602step1 raw26602step1Labels raw26602step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4494 node4494Labels := by rfl

def raw26603 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw26603step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw26603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26603 raw26603Labels = mixedMoment B node4598 node4598Labels := by
  calc
    mixedMoment B raw26603 raw26603Labels = mixedMoment B raw26603step0 raw26603step0Labels := by
      have ha : raw26603step0 = (fun i j => raw26603 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26603step0 raw26603; decide +kernel
      have hl : raw26603step0Labels = raw26603Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26603 raw26603Labels permutation152 permutation6
    mixedMoment B raw26603step0 raw26603step0Labels = mixedMoment B raw26603step1 raw26603step1Labels := by
      have ha : raw26603step1 = raw26603step0 := by apply Matrix.ext; unfold raw26603step1 raw26603step0; decide +kernel
      have hl : raw26603step0Labels = labelEmbedding9 ∘ raw26603step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26603step0 raw26603step0Labels raw26603step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4598 node4598Labels := by rfl

def raw26604 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26604step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26604 raw26604Labels = mixedMoment B node4613 node4613Labels := by
  calc
    mixedMoment B raw26604 raw26604Labels = mixedMoment B raw26604step0 raw26604step0Labels := by
      have hz : ∀ j, raw26604 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26604step0 = (fun i j => raw26604 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26604step0 raw26604; decide +kernel
      have hl : raw26604step0Labels = raw26604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26604 raw26604Labels permutation265 hz
    mixedMoment B raw26604step0 raw26604step0Labels = mixedMoment B raw26604step1 raw26604step1Labels := by
      have ha : raw26604step1 = (fun i j => raw26604step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26604step1 raw26604step0; decide +kernel
      have hl : raw26604step1Labels = raw26604step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26604step0 raw26604step0Labels permutation53 permutation7
    mixedMoment B raw26604step1 raw26604step1Labels = mixedMoment B raw26604step2 raw26604step2Labels := by
      have ha : raw26604step2 = raw26604step1 := by apply Matrix.ext; unfold raw26604step2 raw26604step1; decide +kernel
      have hl : raw26604step1Labels = labelEmbedding10 ∘ raw26604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26604step1 raw26604step1Labels raw26604step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4613 node4613Labels := by rfl

def raw26605 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26605step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26605 raw26605Labels = mixedMoment B node4613 node4613Labels := by
  calc
    mixedMoment B raw26605 raw26605Labels = mixedMoment B raw26605step0 raw26605step0Labels := by
      have hz : ∀ j, raw26605 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26605step0 = (fun i j => raw26605 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26605step0 raw26605; decide +kernel
      have hl : raw26605step0Labels = raw26605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26605 raw26605Labels permutation265 hz
    mixedMoment B raw26605step0 raw26605step0Labels = mixedMoment B raw26605step1 raw26605step1Labels := by
      have ha : raw26605step1 = (fun i j => raw26605step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26605step1 raw26605step0; decide +kernel
      have hl : raw26605step1Labels = raw26605step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26605step0 raw26605step0Labels permutation51 permutation7
    mixedMoment B raw26605step1 raw26605step1Labels = mixedMoment B raw26605step2 raw26605step2Labels := by
      have ha : raw26605step2 = raw26605step1 := by apply Matrix.ext; unfold raw26605step2 raw26605step1; decide +kernel
      have hl : raw26605step1Labels = labelEmbedding10 ∘ raw26605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26605step1 raw26605step1Labels raw26605step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4613 node4613Labels := by rfl

def raw26606 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw26606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw26606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26606step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26606 raw26606Labels = mixedMoment B node4613 node4613Labels := by
  calc
    mixedMoment B raw26606 raw26606Labels = mixedMoment B raw26606step0 raw26606step0Labels := by
      have hz : ∀ j, raw26606 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26606step0 = (fun i j => raw26606 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26606step0 raw26606; decide +kernel
      have hl : raw26606step0Labels = raw26606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26606 raw26606Labels permutation265 hz
    mixedMoment B raw26606step0 raw26606step0Labels = mixedMoment B raw26606step1 raw26606step1Labels := by
      have ha : raw26606step1 = (fun i j => raw26606step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26606step1 raw26606step0; decide +kernel
      have hl : raw26606step1Labels = raw26606step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26606step0 raw26606step0Labels permutation50 permutation7
    mixedMoment B raw26606step1 raw26606step1Labels = mixedMoment B raw26606step2 raw26606step2Labels := by
      have ha : raw26606step2 = raw26606step1 := by apply Matrix.ext; unfold raw26606step2 raw26606step1; decide +kernel
      have hl : raw26606step1Labels = labelEmbedding10 ∘ raw26606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26606step1 raw26606step1Labels raw26606step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4613 node4613Labels := by rfl

def raw26607 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26607step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26607 raw26607Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw26607 raw26607Labels = mixedMoment B raw26607step0 raw26607step0Labels := by
      have ha : raw26607step0 = (fun i j => raw26607 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26607step0 raw26607; decide +kernel
      have hl : raw26607step0Labels = raw26607Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26607 raw26607Labels permutation170 permutation7
    mixedMoment B raw26607step0 raw26607step0Labels = mixedMoment B raw26607step1 raw26607step1Labels := by
      have ha : raw26607step1 = raw26607step0 := by apply Matrix.ext; unfold raw26607step1 raw26607step0; decide +kernel
      have hl : raw26607step0Labels = labelEmbedding1 ∘ raw26607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26607step0 raw26607step0Labels raw26607step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1034 node1034Labels := by rfl

def raw26608 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26608step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26608 raw26608Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw26608 raw26608Labels = mixedMoment B raw26608step0 raw26608step0Labels := by
      have hz : ∀ j, raw26608 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26608step0 = (fun i j => raw26608 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26608step0 raw26608; decide +kernel
      have hl : raw26608step0Labels = raw26608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26608 raw26608Labels permutation265 hz
    mixedMoment B raw26608step0 raw26608step0Labels = mixedMoment B raw26608step1 raw26608step1Labels := by
      have ha : raw26608step1 = (fun i j => raw26608step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26608step1 raw26608step0; decide +kernel
      have hl : raw26608step1Labels = raw26608step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26608step0 raw26608step0Labels permutation53 permutation7
    mixedMoment B raw26608step1 raw26608step1Labels = mixedMoment B raw26608step2 raw26608step2Labels := by
      have ha : raw26608step2 = raw26608step1 := by apply Matrix.ext; unfold raw26608step2 raw26608step1; decide +kernel
      have hl : raw26608step1Labels = labelEmbedding1 ∘ raw26608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26608step1 raw26608step1Labels raw26608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw26609 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26609step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26609 raw26609Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw26609 raw26609Labels = mixedMoment B raw26609step0 raw26609step0Labels := by
      have hz : ∀ j, raw26609 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26609step0 = (fun i j => raw26609 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26609step0 raw26609; decide +kernel
      have hl : raw26609step0Labels = raw26609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26609 raw26609Labels permutation265 hz
    mixedMoment B raw26609step0 raw26609step0Labels = mixedMoment B raw26609step1 raw26609step1Labels := by
      have ha : raw26609step1 = (fun i j => raw26609step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26609step1 raw26609step0; decide +kernel
      have hl : raw26609step1Labels = raw26609step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26609step0 raw26609step0Labels permutation51 permutation7
    mixedMoment B raw26609step1 raw26609step1Labels = mixedMoment B raw26609step2 raw26609step2Labels := by
      have ha : raw26609step2 = raw26609step1 := by apply Matrix.ext; unfold raw26609step2 raw26609step1; decide +kernel
      have hl : raw26609step1Labels = labelEmbedding1 ∘ raw26609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26609step1 raw26609step1Labels raw26609step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw26610 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26610step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26610 raw26610Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw26610 raw26610Labels = mixedMoment B raw26610step0 raw26610step0Labels := by
      have hz : ∀ j, raw26610 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26610step0 = (fun i j => raw26610 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26610step0 raw26610; decide +kernel
      have hl : raw26610step0Labels = raw26610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26610 raw26610Labels permutation265 hz
    mixedMoment B raw26610step0 raw26610step0Labels = mixedMoment B raw26610step1 raw26610step1Labels := by
      have ha : raw26610step1 = (fun i j => raw26610step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26610step1 raw26610step0; decide +kernel
      have hl : raw26610step1Labels = raw26610step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26610step0 raw26610step0Labels permutation50 permutation7
    mixedMoment B raw26610step1 raw26610step1Labels = mixedMoment B raw26610step2 raw26610step2Labels := by
      have ha : raw26610step2 = raw26610step1 := by apply Matrix.ext; unfold raw26610step2 raw26610step1; decide +kernel
      have hl : raw26610step1Labels = labelEmbedding1 ∘ raw26610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26610step1 raw26610step1Labels raw26610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw26611 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26611step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26611 raw26611Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw26611 raw26611Labels = mixedMoment B raw26611step0 raw26611step0Labels := by
      have hz : ∀ j, raw26611 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26611step0 = (fun i j => raw26611 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26611step0 raw26611; decide +kernel
      have hl : raw26611step0Labels = raw26611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26611 raw26611Labels permutation265 hz
    mixedMoment B raw26611step0 raw26611step0Labels = mixedMoment B raw26611step1 raw26611step1Labels := by
      have ha : raw26611step1 = (fun i j => raw26611step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26611step1 raw26611step0; decide +kernel
      have hl : raw26611step1Labels = raw26611step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26611step0 raw26611step0Labels permutation50 permutation7
    mixedMoment B raw26611step1 raw26611step1Labels = mixedMoment B raw26611step2 raw26611step2Labels := by
      have ha : raw26611step2 = raw26611step1 := by apply Matrix.ext; unfold raw26611step2 raw26611step1; decide +kernel
      have hl : raw26611step1Labels = labelEmbedding1 ∘ raw26611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26611step1 raw26611step1Labels raw26611step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1081 node1081Labels := by rfl

def raw26612 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26612 raw26612Labels = mixedMoment B node1405 node1405Labels := by
  calc
    mixedMoment B raw26612 raw26612Labels = mixedMoment B raw26612step0 raw26612step0Labels := by
      have ha : raw26612step0 = (fun i j => raw26612 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26612step0 raw26612; decide +kernel
      have hl : raw26612step0Labels = raw26612Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26612 raw26612Labels permutation170 permutation7
    mixedMoment B raw26612step0 raw26612step0Labels = mixedMoment B raw26612step1 raw26612step1Labels := by
      have ha : raw26612step1 = raw26612step0 := by apply Matrix.ext; unfold raw26612step1 raw26612step0; decide +kernel
      have hl : raw26612step0Labels = labelEmbedding1 ∘ raw26612step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26612step0 raw26612step0Labels raw26612step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1405 node1405Labels := by rfl

def raw26613 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26613step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26613 raw26613Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw26613 raw26613Labels = mixedMoment B raw26613step0 raw26613step0Labels := by
      have ha : raw26613step0 = (fun i j => raw26613 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26613step0 raw26613; decide +kernel
      have hl : raw26613step0Labels = raw26613Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26613 raw26613Labels permutation173 permutation7
    mixedMoment B raw26613step0 raw26613step0Labels = mixedMoment B raw26613step1 raw26613step1Labels := by
      have ha : raw26613step1 = raw26613step0 := by apply Matrix.ext; unfold raw26613step1 raw26613step0; decide +kernel
      have hl : raw26613step0Labels = labelEmbedding1 ∘ raw26613step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26613step0 raw26613step0Labels raw26613step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1228 node1228Labels := by rfl

def raw26614 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26614 raw26614Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw26614 raw26614Labels = mixedMoment B raw26614step0 raw26614step0Labels := by
      have ha : raw26614step0 = (fun i j => raw26614 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26614step0 raw26614; decide +kernel
      have hl : raw26614step0Labels = raw26614Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26614 raw26614Labels permutation171 permutation7
    mixedMoment B raw26614step0 raw26614step0Labels = mixedMoment B raw26614step1 raw26614step1Labels := by
      have ha : raw26614step1 = raw26614step0 := by apply Matrix.ext; unfold raw26614step1 raw26614step0; decide +kernel
      have hl : raw26614step0Labels = labelEmbedding1 ∘ raw26614step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26614step0 raw26614step0Labels raw26614step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1228 node1228Labels := by rfl

def raw26615 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26615 raw26615Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw26615 raw26615Labels = mixedMoment B raw26615step0 raw26615step0Labels := by
      have ha : raw26615step0 = (fun i j => raw26615 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26615step0 raw26615; decide +kernel
      have hl : raw26615step0Labels = raw26615Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26615 raw26615Labels permutation170 permutation7
    mixedMoment B raw26615step0 raw26615step0Labels = mixedMoment B raw26615step1 raw26615step1Labels := by
      have ha : raw26615step1 = raw26615step0 := by apply Matrix.ext; unfold raw26615step1 raw26615step0; decide +kernel
      have hl : raw26615step0Labels = labelEmbedding1 ∘ raw26615step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26615step0 raw26615step0Labels raw26615step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1228 node1228Labels := by rfl

def raw26616 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26616 raw26616Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw26616 raw26616Labels = mixedMoment B raw26616step0 raw26616step0Labels := by
      have ha : raw26616step0 = (fun i j => raw26616 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26616step0 raw26616; decide +kernel
      have hl : raw26616step0Labels = raw26616Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26616 raw26616Labels permutation170 permutation7
    mixedMoment B raw26616step0 raw26616step0Labels = mixedMoment B raw26616step1 raw26616step1Labels := by
      have ha : raw26616step1 = raw26616step0 := by apply Matrix.ext; unfold raw26616step1 raw26616step0; decide +kernel
      have hl : raw26616step0Labels = labelEmbedding1 ∘ raw26616step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26616step0 raw26616step0Labels raw26616step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw26617 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26617 raw26617Labels = mixedMoment B node1441 node1441Labels := by
  calc
    mixedMoment B raw26617 raw26617Labels = mixedMoment B raw26617step0 raw26617step0Labels := by
      have hz : ∀ j, raw26617 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26617step0 = (fun i j => raw26617 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26617step0 raw26617; decide +kernel
      have hl : raw26617step0Labels = raw26617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26617 raw26617Labels permutation265 hz
    mixedMoment B raw26617step0 raw26617step0Labels = mixedMoment B raw26617step1 raw26617step1Labels := by
      have ha : raw26617step1 = (fun i j => raw26617step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26617step1 raw26617step0; decide +kernel
      have hl : raw26617step1Labels = raw26617step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26617step0 raw26617step0Labels permutation50 permutation7
    mixedMoment B raw26617step1 raw26617step1Labels = mixedMoment B raw26617step2 raw26617step2Labels := by
      have ha : raw26617step2 = raw26617step1 := by apply Matrix.ext; unfold raw26617step2 raw26617step1; decide +kernel
      have hl : raw26617step1Labels = labelEmbedding1 ∘ raw26617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26617step1 raw26617step1Labels raw26617step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1441 node1441Labels := by rfl

def raw26618 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26618 raw26618Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26618 raw26618Labels = mixedMoment B raw26618step0 raw26618step0Labels := by
      have ha : raw26618step0 = (fun i j => raw26618 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26618step0 raw26618; decide +kernel
      have hl : raw26618step0Labels = raw26618Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26618 raw26618Labels permutation170 permutation7
    mixedMoment B raw26618step0 raw26618step0Labels = mixedMoment B raw26618step1 raw26618step1Labels := by
      have ha : raw26618step1 = raw26618step0 := by apply Matrix.ext; unfold raw26618step1 raw26618step0; decide +kernel
      have hl : raw26618step0Labels = labelEmbedding1 ∘ raw26618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26618step0 raw26618step0Labels raw26618step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw26619 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26619step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26619 raw26619Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26619 raw26619Labels = mixedMoment B raw26619step0 raw26619step0Labels := by
      have hz : ∀ j, raw26619 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26619step0 = (fun i j => raw26619 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26619step0 raw26619; decide +kernel
      have hl : raw26619step0Labels = raw26619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26619 raw26619Labels permutation265 hz
    mixedMoment B raw26619step0 raw26619step0Labels = mixedMoment B raw26619step1 raw26619step1Labels := by
      have ha : raw26619step1 = (fun i j => raw26619step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26619step1 raw26619step0; decide +kernel
      have hl : raw26619step1Labels = raw26619step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26619step0 raw26619step0Labels permutation51 permutation7
    mixedMoment B raw26619step1 raw26619step1Labels = mixedMoment B raw26619step2 raw26619step2Labels := by
      have ha : raw26619step2 = raw26619step1 := by apply Matrix.ext; unfold raw26619step2 raw26619step1; decide +kernel
      have hl : raw26619step1Labels = labelEmbedding1 ∘ raw26619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26619step1 raw26619step1Labels raw26619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw26620 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26620 raw26620Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26620 raw26620Labels = mixedMoment B raw26620step0 raw26620step0Labels := by
      have hz : ∀ j, raw26620 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26620step0 = (fun i j => raw26620 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26620step0 raw26620; decide +kernel
      have hl : raw26620step0Labels = raw26620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26620 raw26620Labels permutation265 hz
    mixedMoment B raw26620step0 raw26620step0Labels = mixedMoment B raw26620step1 raw26620step1Labels := by
      have ha : raw26620step1 = (fun i j => raw26620step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26620step1 raw26620step0; decide +kernel
      have hl : raw26620step1Labels = raw26620step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26620step0 raw26620step0Labels permutation50 permutation7
    mixedMoment B raw26620step1 raw26620step1Labels = mixedMoment B raw26620step2 raw26620step2Labels := by
      have ha : raw26620step2 = raw26620step1 := by apply Matrix.ext; unfold raw26620step2 raw26620step1; decide +kernel
      have hl : raw26620step1Labels = labelEmbedding1 ∘ raw26620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26620step1 raw26620step1Labels raw26620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw26621 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26621 raw26621Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26621 raw26621Labels = mixedMoment B raw26621step0 raw26621step0Labels := by
      have hz : ∀ j, raw26621 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26621step0 = (fun i j => raw26621 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26621step0 raw26621; decide +kernel
      have hl : raw26621step0Labels = raw26621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26621 raw26621Labels permutation265 hz
    mixedMoment B raw26621step0 raw26621step0Labels = mixedMoment B raw26621step1 raw26621step1Labels := by
      have ha : raw26621step1 = (fun i j => raw26621step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26621step1 raw26621step0; decide +kernel
      have hl : raw26621step1Labels = raw26621step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26621step0 raw26621step0Labels permutation36 permutation7
    mixedMoment B raw26621step1 raw26621step1Labels = mixedMoment B raw26621step2 raw26621step2Labels := by
      have ha : raw26621step2 = raw26621step1 := by apply Matrix.ext; unfold raw26621step2 raw26621step1; decide +kernel
      have hl : raw26621step1Labels = labelEmbedding1 ∘ raw26621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26621step1 raw26621step1Labels raw26621step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw26622 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26622 raw26622Labels = mixedMoment B node1441 node1441Labels := by
  calc
    mixedMoment B raw26622 raw26622Labels = mixedMoment B raw26622step0 raw26622step0Labels := by
      have hz : ∀ j, raw26622 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26622step0 = (fun i j => raw26622 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26622step0 raw26622; decide +kernel
      have hl : raw26622step0Labels = raw26622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26622 raw26622Labels permutation265 hz
    mixedMoment B raw26622step0 raw26622step0Labels = mixedMoment B raw26622step1 raw26622step1Labels := by
      have ha : raw26622step1 = (fun i j => raw26622step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26622step1 raw26622step0; decide +kernel
      have hl : raw26622step1Labels = raw26622step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26622step0 raw26622step0Labels permutation52 permutation7
    mixedMoment B raw26622step1 raw26622step1Labels = mixedMoment B raw26622step2 raw26622step2Labels := by
      have ha : raw26622step2 = raw26622step1 := by apply Matrix.ext; unfold raw26622step2 raw26622step1; decide +kernel
      have hl : raw26622step1Labels = labelEmbedding1 ∘ raw26622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26622step1 raw26622step1Labels raw26622step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1441 node1441Labels := by rfl

def raw26623 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26623 raw26623Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26623 raw26623Labels = mixedMoment B raw26623step0 raw26623step0Labels := by
      have ha : raw26623step0 = (fun i j => raw26623 (permutation172 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26623step0 raw26623; decide +kernel
      have hl : raw26623step0Labels = raw26623Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26623 raw26623Labels permutation172 permutation7
    mixedMoment B raw26623step0 raw26623step0Labels = mixedMoment B raw26623step1 raw26623step1Labels := by
      have ha : raw26623step1 = raw26623step0 := by apply Matrix.ext; unfold raw26623step1 raw26623step0; decide +kernel
      have hl : raw26623step0Labels = labelEmbedding1 ∘ raw26623step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26623step0 raw26623step0Labels raw26623step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1260 node1260Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
