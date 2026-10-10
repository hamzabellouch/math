import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw27136step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw27136step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27136 raw27136Labels = mixedMoment B node4115 node4115Labels := by
  calc
    mixedMoment B raw27136 raw27136Labels = mixedMoment B raw27136step0 raw27136step0Labels := by
      have hz : ∀ j, raw27136 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27136step0 = (fun i j => raw27136 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27136step0 raw27136; decide +kernel
      have hl : raw27136step0Labels = raw27136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27136 raw27136Labels permutation265 hz
    mixedMoment B raw27136step0 raw27136step0Labels = mixedMoment B raw27136step1 raw27136step1Labels := by
      have ha : raw27136step1 = (fun i j => raw27136step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27136step1 raw27136step0; decide +kernel
      have hl : raw27136step1Labels = raw27136step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27136step0 raw27136step0Labels permutation48 permutation3
    mixedMoment B raw27136step1 raw27136step1Labels = mixedMoment B raw27136step2 raw27136step2Labels := by
      have ha : raw27136step2 = raw27136step1 := by apply Matrix.ext; unfold raw27136step2 raw27136step1; decide +kernel
      have hl : raw27136step1Labels = labelEmbedding6 ∘ raw27136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27136step1 raw27136step1Labels raw27136step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4115 node4115Labels := by rfl

def raw27137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw27137step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw27137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27137 raw27137Labels = mixedMoment B node4298 node4298Labels := by
  calc
    mixedMoment B raw27137 raw27137Labels = mixedMoment B raw27137step0 raw27137step0Labels := by
      have ha : raw27137step0 = (fun i j => raw27137 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27137step0 raw27137; decide +kernel
      have hl : raw27137step0Labels = raw27137Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27137 raw27137Labels permutation168 permutation3
    mixedMoment B raw27137step0 raw27137step0Labels = mixedMoment B raw27137step1 raw27137step1Labels := by
      have ha : raw27137step1 = raw27137step0 := by apply Matrix.ext; unfold raw27137step1 raw27137step0; decide +kernel
      have hl : raw27137step0Labels = labelEmbedding6 ∘ raw27137step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27137step0 raw27137step0Labels raw27137step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4298 node4298Labels := by rfl

def raw27138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27138step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27138step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27138 raw27138Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw27138 raw27138Labels = mixedMoment B raw27138step0 raw27138step0Labels := by
      have hz : ∀ j, raw27138 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27138step0 = (fun i j => raw27138 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27138step0 raw27138; decide +kernel
      have hl : raw27138step0Labels = raw27138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27138 raw27138Labels permutation265 hz
    mixedMoment B raw27138step0 raw27138step0Labels = mixedMoment B raw27138step1 raw27138step1Labels := by
      have ha : raw27138step1 = (fun i j => raw27138step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27138step1 raw27138step0; decide +kernel
      have hl : raw27138step1Labels = raw27138step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27138step0 raw27138step0Labels permutation35 permutation3
    mixedMoment B raw27138step1 raw27138step1Labels = mixedMoment B raw27138step2 raw27138step2Labels := by
      have ha : raw27138step2 = raw27138step1 := by apply Matrix.ext; unfold raw27138step2 raw27138step1; decide +kernel
      have hl : raw27138step1Labels = labelEmbedding6 ∘ raw27138step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27138step1 raw27138step1Labels raw27138step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw27139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw27139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw27139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw27139step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw27139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27139 raw27139Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw27139 raw27139Labels = mixedMoment B raw27139step0 raw27139step0Labels := by
      have hz : ∀ j, raw27139 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27139step0 = (fun i j => raw27139 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27139step0 raw27139; decide +kernel
      have hl : raw27139step0Labels = raw27139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27139 raw27139Labels permutation265 hz
    mixedMoment B raw27139step0 raw27139step0Labels = mixedMoment B raw27139step1 raw27139step1Labels := by
      have ha : raw27139step1 = (fun i j => raw27139step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27139step1 raw27139step0; decide +kernel
      have hl : raw27139step1Labels = raw27139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27139step0 raw27139step0Labels permutation48 permutation3
    mixedMoment B raw27139step1 raw27139step1Labels = mixedMoment B raw27139step2 raw27139step2Labels := by
      have ha : raw27139step2 = raw27139step1 := by apply Matrix.ext; unfold raw27139step2 raw27139step1; decide +kernel
      have hl : raw27139step1Labels = labelEmbedding6 ∘ raw27139step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27139step1 raw27139step1Labels raw27139step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw27140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw27140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw27140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw27140step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw27140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27140 raw27140Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw27140 raw27140Labels = mixedMoment B raw27140step0 raw27140step0Labels := by
      have hz : ∀ j, raw27140 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27140step0 = (fun i j => raw27140 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27140step0 raw27140; decide +kernel
      have hl : raw27140step0Labels = raw27140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27140 raw27140Labels permutation265 hz
    mixedMoment B raw27140step0 raw27140step0Labels = mixedMoment B raw27140step1 raw27140step1Labels := by
      have ha : raw27140step1 = (fun i j => raw27140step0 (permutation54 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27140step1 raw27140step0; decide +kernel
      have hl : raw27140step1Labels = raw27140step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27140step0 raw27140step0Labels permutation54 permutation3
    mixedMoment B raw27140step1 raw27140step1Labels = mixedMoment B raw27140step2 raw27140step2Labels := by
      have ha : raw27140step2 = raw27140step1 := by apply Matrix.ext; unfold raw27140step2 raw27140step1; decide +kernel
      have hl : raw27140step1Labels = labelEmbedding6 ∘ raw27140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27140step1 raw27140step1Labels raw27140step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw27141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw27141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw27141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27141 raw27141Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw27141 raw27141Labels = mixedMoment B raw27141step0 raw27141step0Labels := by
      have hz : ∀ j, raw27141 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27141step0 = (fun i j => raw27141 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27141step0 raw27141; decide +kernel
      have hl : raw27141step0Labels = raw27141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27141 raw27141Labels permutation265 hz
    mixedMoment B raw27141step0 raw27141step0Labels = mixedMoment B raw27141step1 raw27141step1Labels := by
      have ha : raw27141step1 = (fun i j => raw27141step0 (permutation52 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27141step1 raw27141step0; decide +kernel
      have hl : raw27141step1Labels = raw27141step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27141step0 raw27141step0Labels permutation52 permutation3
    mixedMoment B raw27141step1 raw27141step1Labels = mixedMoment B raw27141step2 raw27141step2Labels := by
      have ha : raw27141step2 = raw27141step1 := by apply Matrix.ext; unfold raw27141step2 raw27141step1; decide +kernel
      have hl : raw27141step1Labels = labelEmbedding6 ∘ raw27141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27141step1 raw27141step1Labels raw27141step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

def raw27142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw27142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27142step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27142 raw27142Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw27142 raw27142Labels = mixedMoment B raw27142step0 raw27142step0Labels := by
      have ha : raw27142step0 = (fun i j => raw27142 (permutation172 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27142step0 raw27142; decide +kernel
      have hl : raw27142step0Labels = raw27142Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27142 raw27142Labels permutation172 permutation3
    mixedMoment B raw27142step0 raw27142step0Labels = mixedMoment B raw27142step1 raw27142step1Labels := by
      have ha : raw27142step1 = raw27142step0 := by apply Matrix.ext; unfold raw27142step1 raw27142step0; decide +kernel
      have hl : raw27142step0Labels = labelEmbedding6 ∘ raw27142step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27142step0 raw27142step0Labels raw27142step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

def raw27143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw27143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw27143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27143 raw27143Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw27143 raw27143Labels = mixedMoment B raw27143step0 raw27143step0Labels := by
      have hz : ∀ j, raw27143 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27143step0 = (fun i j => raw27143 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27143step0 raw27143; decide +kernel
      have hl : raw27143step0Labels = raw27143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27143 raw27143Labels permutation265 hz
    mixedMoment B raw27143step0 raw27143step0Labels = mixedMoment B raw27143step1 raw27143step1Labels := by
      have ha : raw27143step1 = (fun i j => raw27143step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27143step1 raw27143step0; decide +kernel
      have hl : raw27143step1Labels = raw27143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27143step0 raw27143step0Labels permutation36 permutation3
    mixedMoment B raw27143step1 raw27143step1Labels = mixedMoment B raw27143step2 raw27143step2Labels := by
      have ha : raw27143step2 = raw27143step1 := by apply Matrix.ext; unfold raw27143step2 raw27143step1; decide +kernel
      have hl : raw27143step1Labels = labelEmbedding6 ∘ raw27143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27143step1 raw27143step1Labels raw27143step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw27144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw27144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw27144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw27144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27144step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27144step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27144step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27144step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27144 raw27144Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw27144 raw27144Labels = mixedMoment B raw27144step0 raw27144step0Labels := by
      have hz : ∀ j, raw27144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27144step0 = (fun i j => raw27144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27144step0 raw27144; decide +kernel
      have hl : raw27144step0Labels = raw27144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27144 raw27144Labels permutation434 hz
    mixedMoment B raw27144step0 raw27144step0Labels = mixedMoment B raw27144step1 raw27144step1Labels := by
      have hz : ∀ j, raw27144step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27144step1 = (fun i j => raw27144step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27144step1 raw27144step0; decide +kernel
      have hl : raw27144step1Labels = raw27144step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27144step0 raw27144step0Labels permutation56 hz
    mixedMoment B raw27144step1 raw27144step1Labels = mixedMoment B raw27144step2 raw27144step2Labels := by
      have ha : raw27144step2 = (fun i j => raw27144step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27144step2 raw27144step1; decide +kernel
      have hl : raw27144step2Labels = raw27144step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27144step1 raw27144step1Labels permutation12 permutation3
    mixedMoment B raw27144step2 raw27144step2Labels = mixedMoment B raw27144step3 raw27144step3Labels := by
      have ha : raw27144step3 = raw27144step2 := by apply Matrix.ext; unfold raw27144step3 raw27144step2; decide +kernel
      have hl : raw27144step2Labels = labelEmbedding6 ∘ raw27144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27144step2 raw27144step2Labels raw27144step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw27145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw27145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw27145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27145 raw27145Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw27145 raw27145Labels = mixedMoment B raw27145step0 raw27145step0Labels := by
      have hz : ∀ j, raw27145 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27145step0 = (fun i j => raw27145 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27145step0 raw27145; decide +kernel
      have hl : raw27145step0Labels = raw27145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27145 raw27145Labels permutation265 hz
    mixedMoment B raw27145step0 raw27145step0Labels = mixedMoment B raw27145step1 raw27145step1Labels := by
      have ha : raw27145step1 = (fun i j => raw27145step0 (permutation52 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27145step1 raw27145step0; decide +kernel
      have hl : raw27145step1Labels = raw27145step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27145step0 raw27145step0Labels permutation52 permutation3
    mixedMoment B raw27145step1 raw27145step1Labels = mixedMoment B raw27145step2 raw27145step2Labels := by
      have ha : raw27145step2 = raw27145step1 := by apply Matrix.ext; unfold raw27145step2 raw27145step1; decide +kernel
      have hl : raw27145step1Labels = labelEmbedding6 ∘ raw27145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27145step1 raw27145step1Labels raw27145step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw27146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27146step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27146 raw27146Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw27146 raw27146Labels = mixedMoment B raw27146step0 raw27146step0Labels := by
      have hz : ∀ j, raw27146 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27146step0 = (fun i j => raw27146 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27146step0 raw27146; decide +kernel
      have hl : raw27146step0Labels = raw27146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27146 raw27146Labels permutation265 hz
    mixedMoment B raw27146step0 raw27146step0Labels = mixedMoment B raw27146step1 raw27146step1Labels := by
      have ha : raw27146step1 = (fun i j => raw27146step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27146step1 raw27146step0; decide +kernel
      have hl : raw27146step1Labels = raw27146step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27146step0 raw27146step0Labels permutation46 permutation3
    mixedMoment B raw27146step1 raw27146step1Labels = mixedMoment B raw27146step2 raw27146step2Labels := by
      have ha : raw27146step2 = raw27146step1 := by apply Matrix.ext; unfold raw27146step2 raw27146step1; decide +kernel
      have hl : raw27146step1Labels = labelEmbedding6 ∘ raw27146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27146step1 raw27146step1Labels raw27146step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

def raw27147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27147step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27147 raw27147Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw27147 raw27147Labels = mixedMoment B raw27147step0 raw27147step0Labels := by
      have ha : raw27147step0 = (fun i j => raw27147 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27147step0 raw27147; decide +kernel
      have hl : raw27147step0Labels = raw27147Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27147 raw27147Labels permutation166 permutation3
    mixedMoment B raw27147step0 raw27147step0Labels = mixedMoment B raw27147step1 raw27147step1Labels := by
      have ha : raw27147step1 = raw27147step0 := by apply Matrix.ext; unfold raw27147step1 raw27147step0; decide +kernel
      have hl : raw27147step0Labels = labelEmbedding6 ∘ raw27147step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27147step0 raw27147step0Labels raw27147step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

def raw27148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27148 raw27148Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw27148 raw27148Labels = mixedMoment B raw27148step0 raw27148step0Labels := by
      have hz : ∀ j, raw27148 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27148step0 = (fun i j => raw27148 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27148step0 raw27148; decide +kernel
      have hl : raw27148step0Labels = raw27148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27148 raw27148Labels permutation265 hz
    mixedMoment B raw27148step0 raw27148step0Labels = mixedMoment B raw27148step1 raw27148step1Labels := by
      have ha : raw27148step1 = (fun i j => raw27148step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27148step1 raw27148step0; decide +kernel
      have hl : raw27148step1Labels = raw27148step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27148step0 raw27148step0Labels permutation34 permutation3
    mixedMoment B raw27148step1 raw27148step1Labels = mixedMoment B raw27148step2 raw27148step2Labels := by
      have ha : raw27148step2 = raw27148step1 := by apply Matrix.ext; unfold raw27148step2 raw27148step1; decide +kernel
      have hl : raw27148step1Labels = labelEmbedding6 ∘ raw27148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27148step1 raw27148step1Labels raw27148step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw27149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw27149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw27149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27149step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27149step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27149step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27149 raw27149Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw27149 raw27149Labels = mixedMoment B raw27149step0 raw27149step0Labels := by
      have hz : ∀ j, raw27149 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27149step0 = (fun i j => raw27149 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27149step0 raw27149; decide +kernel
      have hl : raw27149step0Labels = raw27149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27149 raw27149Labels permutation434 hz
    mixedMoment B raw27149step0 raw27149step0Labels = mixedMoment B raw27149step1 raw27149step1Labels := by
      have hz : ∀ j, raw27149step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27149step1 = (fun i j => raw27149step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27149step1 raw27149step0; decide +kernel
      have hl : raw27149step1Labels = raw27149step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27149step0 raw27149step0Labels permutation56 hz
    mixedMoment B raw27149step1 raw27149step1Labels = mixedMoment B raw27149step2 raw27149step2Labels := by
      have ha : raw27149step2 = (fun i j => raw27149step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27149step2 raw27149step1; decide +kernel
      have hl : raw27149step2Labels = raw27149step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27149step1 raw27149step1Labels permutation10 permutation3
    mixedMoment B raw27149step2 raw27149step2Labels = mixedMoment B raw27149step3 raw27149step3Labels := by
      have ha : raw27149step3 = raw27149step2 := by apply Matrix.ext; unfold raw27149step3 raw27149step2; decide +kernel
      have hl : raw27149step2Labels = labelEmbedding6 ∘ raw27149step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27149step2 raw27149step2Labels raw27149step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw27150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw27150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw27150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27150 raw27150Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw27150 raw27150Labels = mixedMoment B raw27150step0 raw27150step0Labels := by
      have hz : ∀ j, raw27150 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27150step0 = (fun i j => raw27150 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27150step0 raw27150; decide +kernel
      have hl : raw27150step0Labels = raw27150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27150 raw27150Labels permutation265 hz
    mixedMoment B raw27150step0 raw27150step0Labels = mixedMoment B raw27150step1 raw27150step1Labels := by
      have ha : raw27150step1 = (fun i j => raw27150step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27150step1 raw27150step0; decide +kernel
      have hl : raw27150step1Labels = raw27150step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27150step0 raw27150step0Labels permutation46 permutation3
    mixedMoment B raw27150step1 raw27150step1Labels = mixedMoment B raw27150step2 raw27150step2Labels := by
      have ha : raw27150step2 = raw27150step1 := by apply Matrix.ext; unfold raw27150step2 raw27150step1; decide +kernel
      have hl : raw27150step1Labels = labelEmbedding6 ∘ raw27150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27150step1 raw27150step1Labels raw27150step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw27151 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27151step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27151step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27151 raw27151Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw27151 raw27151Labels = mixedMoment B raw27151step0 raw27151step0Labels := by
      have hz : ∀ j, raw27151 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27151step0 = (fun i j => raw27151 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27151step0 raw27151; decide +kernel
      have hl : raw27151step0Labels = raw27151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27151 raw27151Labels permutation265 hz
    mixedMoment B raw27151step0 raw27151step0Labels = mixedMoment B raw27151step1 raw27151step1Labels := by
      have ha : raw27151step1 = (fun i j => raw27151step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27151step1 raw27151step0; decide +kernel
      have hl : raw27151step1Labels = raw27151step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27151step0 raw27151step0Labels permutation32 permutation7
    mixedMoment B raw27151step1 raw27151step1Labels = mixedMoment B raw27151step2 raw27151step2Labels := by
      have ha : raw27151step2 = raw27151step1 := by apply Matrix.ext; unfold raw27151step2 raw27151step1; decide +kernel
      have hl : raw27151step1Labels = labelEmbedding10 ∘ raw27151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27151step1 raw27151step1Labels raw27151step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw27152 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27152step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27152 raw27152Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw27152 raw27152Labels = mixedMoment B raw27152step0 raw27152step0Labels := by
      have hz : ∀ j, raw27152 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27152step0 = (fun i j => raw27152 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27152step0 raw27152; decide +kernel
      have hl : raw27152step0Labels = raw27152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27152 raw27152Labels permutation265 hz
    mixedMoment B raw27152step0 raw27152step0Labels = mixedMoment B raw27152step1 raw27152step1Labels := by
      have ha : raw27152step1 = (fun i j => raw27152step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27152step1 raw27152step0; decide +kernel
      have hl : raw27152step1Labels = raw27152step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27152step0 raw27152step0Labels permutation49 permutation6
    mixedMoment B raw27152step1 raw27152step1Labels = mixedMoment B raw27152step2 raw27152step2Labels := by
      have ha : raw27152step2 = raw27152step1 := by apply Matrix.ext; unfold raw27152step2 raw27152step1; decide +kernel
      have hl : raw27152step1Labels = labelEmbedding9 ∘ raw27152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27152step1 raw27152step1Labels raw27152step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw27153 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27153step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27153 raw27153Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw27153 raw27153Labels = mixedMoment B raw27153step0 raw27153step0Labels := by
      have hz : ∀ j, raw27153 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27153step0 = (fun i j => raw27153 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27153step0 raw27153; decide +kernel
      have hl : raw27153step0Labels = raw27153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27153 raw27153Labels permutation265 hz
    mixedMoment B raw27153step0 raw27153step0Labels = mixedMoment B raw27153step1 raw27153step1Labels := by
      have ha : raw27153step1 = (fun i j => raw27153step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27153step1 raw27153step0; decide +kernel
      have hl : raw27153step1Labels = raw27153step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27153step0 raw27153step0Labels permutation55 permutation6
    mixedMoment B raw27153step1 raw27153step1Labels = mixedMoment B raw27153step2 raw27153step2Labels := by
      have ha : raw27153step2 = raw27153step1 := by apply Matrix.ext; unfold raw27153step2 raw27153step1; decide +kernel
      have hl : raw27153step1Labels = labelEmbedding9 ∘ raw27153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27153step1 raw27153step1Labels raw27153step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw27154 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27154step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27154 raw27154Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27154 raw27154Labels = mixedMoment B raw27154step0 raw27154step0Labels := by
      have ha : raw27154step0 = (fun i j => raw27154 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27154step0 raw27154; decide +kernel
      have hl : raw27154step0Labels = raw27154Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27154 raw27154Labels permutation168 permutation6
    mixedMoment B raw27154step0 raw27154step0Labels = mixedMoment B raw27154step1 raw27154step1Labels := by
      have ha : raw27154step1 = raw27154step0 := by apply Matrix.ext; unfold raw27154step1 raw27154step0; decide +kernel
      have hl : raw27154step0Labels = labelEmbedding9 ∘ raw27154step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27154step0 raw27154step0Labels raw27154step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27155 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27155step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27155step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27155step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27155step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27155 raw27155Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw27155 raw27155Labels = mixedMoment B raw27155step0 raw27155step0Labels := by
      have hz : ∀ j, raw27155 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27155step0 = (fun i j => raw27155 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27155step0 raw27155; decide +kernel
      have hl : raw27155step0Labels = raw27155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27155 raw27155Labels permutation265 hz
    mixedMoment B raw27155step0 raw27155step0Labels = mixedMoment B raw27155step1 raw27155step1Labels := by
      have ha : raw27155step1 = (fun i j => raw27155step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27155step1 raw27155step0; decide +kernel
      have hl : raw27155step1Labels = raw27155step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27155step0 raw27155step0Labels permutation49 permutation4
    mixedMoment B raw27155step1 raw27155step1Labels = mixedMoment B raw27155step2 raw27155step2Labels := by
      have ha : raw27155step2 = -raw27155step1 := by apply Matrix.ext; change ∀ i j, raw27155step2 i j = -(raw27155step1 i j); unfold raw27155step2 raw27155step1; decide +kernel
      have hl : raw27155step2Labels = raw27155step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27155step2 raw27155step2Labels = mixedMoment B raw27155step3 raw27155step3Labels := by
      have ha : raw27155step3 = raw27155step2 := by apply Matrix.ext; unfold raw27155step3 raw27155step2; decide +kernel
      have hl : raw27155step2Labels = labelEmbedding7 ∘ raw27155step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27155step2 raw27155step2Labels raw27155step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

def raw27156 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27156step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27156 raw27156Labels = mixedMoment B node4414 node4414Labels := by
  calc
    mixedMoment B raw27156 raw27156Labels = mixedMoment B raw27156step0 raw27156step0Labels := by
      have ha : raw27156step0 = (fun i j => raw27156 (permutation169 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27156step0 raw27156; decide +kernel
      have hl : raw27156step0Labels = raw27156Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27156 raw27156Labels permutation169 permutation6
    mixedMoment B raw27156step0 raw27156step0Labels = mixedMoment B raw27156step1 raw27156step1Labels := by
      have ha : raw27156step1 = raw27156step0 := by apply Matrix.ext; unfold raw27156step1 raw27156step0; decide +kernel
      have hl : raw27156step0Labels = labelEmbedding9 ∘ raw27156step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27156step0 raw27156step0Labels raw27156step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4414 node4414Labels := by rfl

def raw27157 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27157step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27157 raw27157Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw27157 raw27157Labels = mixedMoment B raw27157step0 raw27157step0Labels := by
      have hz : ∀ j, raw27157 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27157step0 = (fun i j => raw27157 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27157step0 raw27157; decide +kernel
      have hl : raw27157step0Labels = raw27157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27157 raw27157Labels permutation265 hz
    mixedMoment B raw27157step0 raw27157step0Labels = mixedMoment B raw27157step1 raw27157step1Labels := by
      have ha : raw27157step1 = (fun i j => raw27157step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27157step1 raw27157step0; decide +kernel
      have hl : raw27157step1Labels = raw27157step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27157step0 raw27157step0Labels permutation41 permutation6
    mixedMoment B raw27157step1 raw27157step1Labels = mixedMoment B raw27157step2 raw27157step2Labels := by
      have ha : raw27157step2 = raw27157step1 := by apply Matrix.ext; unfold raw27157step2 raw27157step1; decide +kernel
      have hl : raw27157step1Labels = labelEmbedding9 ∘ raw27157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27157step1 raw27157step1Labels raw27157step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4494 node4494Labels := by rfl

def raw27158 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27158step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27158step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27158 raw27158Labels = mixedMoment B node4486 node4486Labels := by
  calc
    mixedMoment B raw27158 raw27158Labels = mixedMoment B raw27158step0 raw27158step0Labels := by
      have hz : ∀ j, raw27158 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27158step0 = (fun i j => raw27158 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27158step0 raw27158; decide +kernel
      have hl : raw27158step0Labels = raw27158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27158 raw27158Labels permutation265 hz
    mixedMoment B raw27158step0 raw27158step0Labels = mixedMoment B raw27158step1 raw27158step1Labels := by
      have ha : raw27158step1 = (fun i j => raw27158step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27158step1 raw27158step0; decide +kernel
      have hl : raw27158step1Labels = raw27158step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27158step0 raw27158step0Labels permutation49 permutation6
    mixedMoment B raw27158step1 raw27158step1Labels = mixedMoment B raw27158step2 raw27158step2Labels := by
      have ha : raw27158step2 = raw27158step1 := by apply Matrix.ext; unfold raw27158step2 raw27158step1; decide +kernel
      have hl : raw27158step1Labels = labelEmbedding9 ∘ raw27158step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27158step1 raw27158step1Labels raw27158step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4486 node4486Labels := by rfl

def raw27159 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27159step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27159step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27159 raw27159Labels = mixedMoment B node4486 node4486Labels := by
  calc
    mixedMoment B raw27159 raw27159Labels = mixedMoment B raw27159step0 raw27159step0Labels := by
      have hz : ∀ j, raw27159 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27159step0 = (fun i j => raw27159 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27159step0 raw27159; decide +kernel
      have hl : raw27159step0Labels = raw27159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27159 raw27159Labels permutation265 hz
    mixedMoment B raw27159step0 raw27159step0Labels = mixedMoment B raw27159step1 raw27159step1Labels := by
      have ha : raw27159step1 = (fun i j => raw27159step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27159step1 raw27159step0; decide +kernel
      have hl : raw27159step1Labels = raw27159step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27159step0 raw27159step0Labels permutation55 permutation6
    mixedMoment B raw27159step1 raw27159step1Labels = mixedMoment B raw27159step2 raw27159step2Labels := by
      have ha : raw27159step2 = raw27159step1 := by apply Matrix.ext; unfold raw27159step2 raw27159step1; decide +kernel
      have hl : raw27159step1Labels = labelEmbedding9 ∘ raw27159step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27159step1 raw27159step1Labels raw27159step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4486 node4486Labels := by rfl

def raw27160 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw27160step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw27160step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27160step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw27160step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27160 raw27160Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw27160 raw27160Labels = mixedMoment B raw27160step0 raw27160step0Labels := by
      have hz : ∀ j, raw27160 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27160step0 = (fun i j => raw27160 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27160step0 raw27160; decide +kernel
      have hl : raw27160step0Labels = raw27160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27160 raw27160Labels permutation265 hz
    mixedMoment B raw27160step0 raw27160step0Labels = mixedMoment B raw27160step1 raw27160step1Labels := by
      have ha : raw27160step1 = (fun i j => raw27160step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27160step1 raw27160step0; decide +kernel
      have hl : raw27160step1Labels = raw27160step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27160step0 raw27160step0Labels permutation48 permutation4
    mixedMoment B raw27160step1 raw27160step1Labels = mixedMoment B raw27160step2 raw27160step2Labels := by
      have ha : raw27160step2 = -raw27160step1 := by apply Matrix.ext; change ∀ i j, raw27160step2 i j = -(raw27160step1 i j); unfold raw27160step2 raw27160step1; decide +kernel
      have hl : raw27160step2Labels = raw27160step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27160step2 raw27160step2Labels = mixedMoment B raw27160step3 raw27160step3Labels := by
      have ha : raw27160step3 = raw27160step2 := by apply Matrix.ext; unfold raw27160step3 raw27160step2; decide +kernel
      have hl : raw27160step2Labels = labelEmbedding7 ∘ raw27160step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27160step2 raw27160step2Labels raw27160step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

def raw27161 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27161step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27161 raw27161Labels = mixedMoment B node4415 node4415Labels := by
  calc
    mixedMoment B raw27161 raw27161Labels = mixedMoment B raw27161step0 raw27161step0Labels := by
      have ha : raw27161step0 = (fun i j => raw27161 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27161step0 raw27161; decide +kernel
      have hl : raw27161step0Labels = raw27161Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27161 raw27161Labels permutation168 permutation6
    mixedMoment B raw27161step0 raw27161step0Labels = mixedMoment B raw27161step1 raw27161step1Labels := by
      have ha : raw27161step1 = raw27161step0 := by apply Matrix.ext; unfold raw27161step1 raw27161step0; decide +kernel
      have hl : raw27161step0Labels = labelEmbedding9 ∘ raw27161step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27161step0 raw27161step0Labels raw27161step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4415 node4415Labels := by rfl

def raw27162 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![1, -2, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27162step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27162 raw27162Labels = mixedMoment B node4487 node4487Labels := by
  calc
    mixedMoment B raw27162 raw27162Labels = mixedMoment B raw27162step0 raw27162step0Labels := by
      have hz : ∀ j, raw27162 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27162step0 = (fun i j => raw27162 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27162step0 raw27162; decide +kernel
      have hl : raw27162step0Labels = raw27162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27162 raw27162Labels permutation265 hz
    mixedMoment B raw27162step0 raw27162step0Labels = mixedMoment B raw27162step1 raw27162step1Labels := by
      have ha : raw27162step1 = (fun i j => raw27162step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27162step1 raw27162step0; decide +kernel
      have hl : raw27162step1Labels = raw27162step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27162step0 raw27162step0Labels permutation48 permutation6
    mixedMoment B raw27162step1 raw27162step1Labels = mixedMoment B raw27162step2 raw27162step2Labels := by
      have ha : raw27162step2 = raw27162step1 := by apply Matrix.ext; unfold raw27162step2 raw27162step1; decide +kernel
      have hl : raw27162step1Labels = labelEmbedding9 ∘ raw27162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27162step1 raw27162step1Labels raw27162step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4487 node4487Labels := by rfl

def raw27163 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27163step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27163step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27163 raw27163Labels = mixedMoment B node4487 node4487Labels := by
  calc
    mixedMoment B raw27163 raw27163Labels = mixedMoment B raw27163step0 raw27163step0Labels := by
      have hz : ∀ j, raw27163 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27163step0 = (fun i j => raw27163 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27163step0 raw27163; decide +kernel
      have hl : raw27163step0Labels = raw27163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27163 raw27163Labels permutation265 hz
    mixedMoment B raw27163step0 raw27163step0Labels = mixedMoment B raw27163step1 raw27163step1Labels := by
      have ha : raw27163step1 = (fun i j => raw27163step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27163step1 raw27163step0; decide +kernel
      have hl : raw27163step1Labels = raw27163step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27163step0 raw27163step0Labels permutation54 permutation6
    mixedMoment B raw27163step1 raw27163step1Labels = mixedMoment B raw27163step2 raw27163step2Labels := by
      have ha : raw27163step2 = raw27163step1 := by apply Matrix.ext; unfold raw27163step2 raw27163step1; decide +kernel
      have hl : raw27163step1Labels = labelEmbedding9 ∘ raw27163step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27163step1 raw27163step1Labels raw27163step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4487 node4487Labels := by rfl

def raw27164 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw27164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw27164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27164step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27164step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27164step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27164step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27164 raw27164Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw27164 raw27164Labels = mixedMoment B raw27164step0 raw27164step0Labels := by
      have hz : ∀ j, raw27164 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27164step0 = (fun i j => raw27164 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27164step0 raw27164; decide +kernel
      have hl : raw27164step0Labels = raw27164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27164 raw27164Labels permutation265 hz
    mixedMoment B raw27164step0 raw27164step0Labels = mixedMoment B raw27164step1 raw27164step1Labels := by
      have ha : raw27164step1 = (fun i j => raw27164step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27164step1 raw27164step0; decide +kernel
      have hl : raw27164step1Labels = raw27164step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27164step0 raw27164step0Labels permutation53 permutation4
    mixedMoment B raw27164step1 raw27164step1Labels = mixedMoment B raw27164step2 raw27164step2Labels := by
      have ha : raw27164step2 = -raw27164step1 := by apply Matrix.ext; change ∀ i j, raw27164step2 i j = -(raw27164step1 i j); unfold raw27164step2 raw27164step1; decide +kernel
      have hl : raw27164step2Labels = raw27164step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27164step2 raw27164step2Labels = mixedMoment B raw27164step3 raw27164step3Labels := by
      have ha : raw27164step3 = raw27164step2 := by apply Matrix.ext; unfold raw27164step3 raw27164step2; decide +kernel
      have hl : raw27164step2Labels = labelEmbedding7 ∘ raw27164step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27164step2 raw27164step2Labels raw27164step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw27165 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw27165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw27165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27165step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27165 raw27165Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw27165 raw27165Labels = mixedMoment B raw27165step0 raw27165step0Labels := by
      have hz : ∀ j, raw27165 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27165step0 = (fun i j => raw27165 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27165step0 raw27165; decide +kernel
      have hl : raw27165step0Labels = raw27165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27165 raw27165Labels permutation265 hz
    mixedMoment B raw27165step0 raw27165step0Labels = mixedMoment B raw27165step1 raw27165step1Labels := by
      have ha : raw27165step1 = (fun i j => raw27165step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27165step1 raw27165step0; decide +kernel
      have hl : raw27165step1Labels = raw27165step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27165step0 raw27165step0Labels permutation43 permutation6
    mixedMoment B raw27165step1 raw27165step1Labels = mixedMoment B raw27165step2 raw27165step2Labels := by
      have ha : raw27165step2 = raw27165step1 := by apply Matrix.ext; unfold raw27165step2 raw27165step1; decide +kernel
      have hl : raw27165step1Labels = labelEmbedding9 ∘ raw27165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27165step1 raw27165step1Labels raw27165step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw27166 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw27166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw27166step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27166step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27166step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27166step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27166 raw27166Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw27166 raw27166Labels = mixedMoment B raw27166step0 raw27166step0Labels := by
      have hz : ∀ j, raw27166 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27166step0 = (fun i j => raw27166 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27166step0 raw27166; decide +kernel
      have hl : raw27166step0Labels = raw27166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27166 raw27166Labels permutation265 hz
    mixedMoment B raw27166step0 raw27166step0Labels = mixedMoment B raw27166step1 raw27166step1Labels := by
      have ha : raw27166step1 = (fun i j => raw27166step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27166step1 raw27166step0; decide +kernel
      have hl : raw27166step1Labels = raw27166step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27166step0 raw27166step0Labels permutation53 permutation6
    mixedMoment B raw27166step1 raw27166step1Labels = mixedMoment B raw27166step2 raw27166step2Labels := by
      have ha : raw27166step2 = raw27166step1 := by apply Matrix.ext; unfold raw27166step2 raw27166step1; decide +kernel
      have hl : raw27166step1Labels = labelEmbedding9 ∘ raw27166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27166step1 raw27166step1Labels raw27166step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw27167 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27167step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27167step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27167step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27167step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27167 raw27167Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw27167 raw27167Labels = mixedMoment B raw27167step0 raw27167step0Labels := by
      have hz : ∀ j, raw27167 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27167step0 = (fun i j => raw27167 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27167step0 raw27167; decide +kernel
      have hl : raw27167step0Labels = raw27167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27167 raw27167Labels permutation265 hz
    mixedMoment B raw27167step0 raw27167step0Labels = mixedMoment B raw27167step1 raw27167step1Labels := by
      have ha : raw27167step1 = (fun i j => raw27167step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27167step1 raw27167step0; decide +kernel
      have hl : raw27167step1Labels = raw27167step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27167step0 raw27167step0Labels permutation47 permutation4
    mixedMoment B raw27167step1 raw27167step1Labels = mixedMoment B raw27167step2 raw27167step2Labels := by
      have ha : raw27167step2 = -raw27167step1 := by apply Matrix.ext; change ∀ i j, raw27167step2 i j = -(raw27167step1 i j); unfold raw27167step2 raw27167step1; decide +kernel
      have hl : raw27167step2Labels = raw27167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27167step2 raw27167step2Labels = mixedMoment B raw27167step3 raw27167step3Labels := by
      have ha : raw27167step3 = raw27167step2 := by apply Matrix.ext; unfold raw27167step3 raw27167step2; decide +kernel
      have hl : raw27167step2Labels = labelEmbedding7 ∘ raw27167step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27167step2 raw27167step2Labels raw27167step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw27168 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27168step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27168step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27168 raw27168Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw27168 raw27168Labels = mixedMoment B raw27168step0 raw27168step0Labels := by
      have ha : raw27168step0 = (fun i j => raw27168 (permutation167 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27168step0 raw27168; decide +kernel
      have hl : raw27168step0Labels = raw27168Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27168 raw27168Labels permutation167 permutation6
    mixedMoment B raw27168step0 raw27168step0Labels = mixedMoment B raw27168step1 raw27168step1Labels := by
      have ha : raw27168step1 = raw27168step0 := by apply Matrix.ext; unfold raw27168step1 raw27168step0; decide +kernel
      have hl : raw27168step0Labels = labelEmbedding9 ∘ raw27168step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27168step0 raw27168step0Labels raw27168step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw27169 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27169step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27169step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27169 raw27169Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw27169 raw27169Labels = mixedMoment B raw27169step0 raw27169step0Labels := by
      have hz : ∀ j, raw27169 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27169step0 = (fun i j => raw27169 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27169step0 raw27169; decide +kernel
      have hl : raw27169step0Labels = raw27169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27169 raw27169Labels permutation265 hz
    mixedMoment B raw27169step0 raw27169step0Labels = mixedMoment B raw27169step1 raw27169step1Labels := by
      have ha : raw27169step1 = (fun i j => raw27169step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27169step1 raw27169step0; decide +kernel
      have hl : raw27169step1Labels = raw27169step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27169step0 raw27169step0Labels permutation41 permutation6
    mixedMoment B raw27169step1 raw27169step1Labels = mixedMoment B raw27169step2 raw27169step2Labels := by
      have ha : raw27169step2 = raw27169step1 := by apply Matrix.ext; unfold raw27169step2 raw27169step1; decide +kernel
      have hl : raw27169step1Labels = labelEmbedding9 ∘ raw27169step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27169step1 raw27169step1Labels raw27169step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw27170 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw27170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw27170step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27170step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27170step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27170 raw27170Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw27170 raw27170Labels = mixedMoment B raw27170step0 raw27170step0Labels := by
      have hz : ∀ j, raw27170 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27170step0 = (fun i j => raw27170 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27170step0 raw27170; decide +kernel
      have hl : raw27170step0Labels = raw27170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27170 raw27170Labels permutation265 hz
    mixedMoment B raw27170step0 raw27170step0Labels = mixedMoment B raw27170step1 raw27170step1Labels := by
      have ha : raw27170step1 = (fun i j => raw27170step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27170step1 raw27170step0; decide +kernel
      have hl : raw27170step1Labels = raw27170step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27170step0 raw27170step0Labels permutation47 permutation6
    mixedMoment B raw27170step1 raw27170step1Labels = mixedMoment B raw27170step2 raw27170step2Labels := by
      have ha : raw27170step2 = raw27170step1 := by apply Matrix.ext; unfold raw27170step2 raw27170step1; decide +kernel
      have hl : raw27170step1Labels = labelEmbedding9 ∘ raw27170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27170step1 raw27170step1Labels raw27170step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw27171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27171 raw27171Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw27171 raw27171Labels = mixedMoment B raw27171step0 raw27171step0Labels := by
      have ha : raw27171step0 = (fun i j => raw27171 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27171step0 raw27171; decide +kernel
      have hl : raw27171step0Labels = raw27171Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27171 raw27171Labels permutation170 permutation2
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw27172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27172 raw27172Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw27172 raw27172Labels = mixedMoment B raw27172step0 raw27172step0Labels := by
      have hz : ∀ j, raw27172 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27172step0 = (fun i j => raw27172 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27172step0 raw27172; decide +kernel
      have hl : raw27172step0Labels = raw27172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27172 raw27172Labels permutation265 hz
    mixedMoment B raw27172step0 raw27172step0Labels = mixedMoment B raw27172step1 raw27172step1Labels := by
      have ha : raw27172step1 = (fun i j => raw27172step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27172step1 raw27172step0; decide +kernel
      have hl : raw27172step1Labels = raw27172step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27172step0 raw27172step0Labels permutation36 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw27173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27173 raw27173Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw27173 raw27173Labels = mixedMoment B raw27173step0 raw27173step0Labels := by
      have hz : ∀ j, raw27173 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27173step0 = (fun i j => raw27173 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27173step0 raw27173; decide +kernel
      have hl : raw27173step0Labels = raw27173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27173 raw27173Labels permutation265 hz
    mixedMoment B raw27173step0 raw27173step0Labels = mixedMoment B raw27173step1 raw27173step1Labels := by
      have ha : raw27173step1 = (fun i j => raw27173step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27173step1 raw27173step0; decide +kernel
      have hl : raw27173step1Labels = raw27173step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27173step0 raw27173step0Labels permutation42 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw27174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27174step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27174 raw27174Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw27174 raw27174Labels = mixedMoment B raw27174step0 raw27174step0Labels := by
      have hz : ∀ j, raw27174 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27174step0 = (fun i j => raw27174 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27174step0 raw27174; decide +kernel
      have hl : raw27174step0Labels = raw27174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27174 raw27174Labels permutation265 hz
    mixedMoment B raw27174step0 raw27174step0Labels = mixedMoment B raw27174step1 raw27174step1Labels := by
      have ha : raw27174step1 = (fun i j => raw27174step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27174step1 raw27174step0; decide +kernel
      have hl : raw27174step1Labels = raw27174step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27174step0 raw27174step0Labels permutation48 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw27175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27175step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27175step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw27175step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw27175step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw27175step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27175 raw27175Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw27175 raw27175Labels = mixedMoment B raw27175step0 raw27175step0Labels := by
      have hz : ∀ j, raw27175 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27175step0 = (fun i j => raw27175 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27175step0 raw27175; decide +kernel
      have hl : raw27175step0Labels = raw27175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27175 raw27175Labels permutation590 hz
    mixedMoment B raw27175step0 raw27175step0Labels = mixedMoment B raw27175step1 raw27175step1Labels := by
      have hz : ∀ j, raw27175step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27175step1 = (fun i j => raw27175step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27175step1 raw27175step0; decide +kernel
      have hl : raw27175step1Labels = raw27175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27175step0 raw27175step0Labels permutation56 hz
    mixedMoment B raw27175step1 raw27175step1Labels = mixedMoment B raw27175step2 raw27175step2Labels := by
      have hz : ∀ i, raw27175step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw27175step2 = (fun i j => raw27175step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw27175step2 raw27175step1; decide +kernel
      have hl : raw27175step2Labels = (fun j => raw27175step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27175step1 raw27175step1Labels permutation4 hz
    mixedMoment B raw27175step2 raw27175step2Labels = mixedMoment B raw27175step3 raw27175step3Labels := by
      have ha : raw27175step3 = raw27175step2 := by apply Matrix.ext; unfold raw27175step3 raw27175step2; decide +kernel
      have hl : raw27175step2Labels = labelEmbedding2 ∘ raw27175step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27175step2 raw27175step2Labels raw27175step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw27176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27176 raw27176Labels = mixedMoment B node4171 node4171Labels := by
  calc
    mixedMoment B raw27176 raw27176Labels = mixedMoment B raw27176step0 raw27176step0Labels := by
      have ha : raw27176step0 = (fun i j => raw27176 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27176step0 raw27176; decide +kernel
      have hl : raw27176step0Labels = raw27176Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27176 raw27176Labels permutation170 permutation2
    _ = mixedMoment B node4171 node4171Labels := by rfl

def raw27177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27177step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27177 raw27177Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27177 raw27177Labels = mixedMoment B raw27177step0 raw27177step0Labels := by
      have ha : raw27177step0 = (fun i j => raw27177 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27177step0 raw27177; decide +kernel
      have hl : raw27177step0Labels = raw27177Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27177 raw27177Labels permutation180 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27178step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27178 raw27178Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27178 raw27178Labels = mixedMoment B raw27178step0 raw27178step0Labels := by
      have ha : raw27178step0 = (fun i j => raw27178 (permutation204 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27178step0 raw27178; decide +kernel
      have hl : raw27178step0Labels = raw27178Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27178 raw27178Labels permutation204 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27179 raw27179Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27179 raw27179Labels = mixedMoment B raw27179step0 raw27179step0Labels := by
      have ha : raw27179step0 = (fun i j => raw27179 (permutation228 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27179step0 raw27179; decide +kernel
      have hl : raw27179step0Labels = raw27179Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27179 raw27179Labels permutation228 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27180 raw27180Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw27180 raw27180Labels = mixedMoment B raw27180step0 raw27180step0Labels := by
      have hz : ∀ j, raw27180 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27180step0 = (fun i j => raw27180 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27180step0 raw27180; decide +kernel
      have hl : raw27180step0Labels = raw27180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27180 raw27180Labels permutation590 hz
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw27181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27181 raw27181Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw27181 raw27181Labels = mixedMoment B raw27181step0 raw27181step0Labels := by
      have hz : ∀ j, raw27181 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27181step0 = (fun i j => raw27181 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27181step0 raw27181; decide +kernel
      have hl : raw27181step0Labels = raw27181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27181 raw27181Labels permutation265 hz
    mixedMoment B raw27181step0 raw27181step0Labels = mixedMoment B raw27181step1 raw27181step1Labels := by
      have ha : raw27181step1 = (fun i j => raw27181step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27181step1 raw27181step0; decide +kernel
      have hl : raw27181step1Labels = raw27181step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27181step0 raw27181step0Labels permutation53 permutation2
    _ = mixedMoment B node4175 node4175Labels := by rfl

def raw27182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27182 raw27182Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw27182 raw27182Labels = mixedMoment B raw27182step0 raw27182step0Labels := by
      have ha : raw27182step0 = (fun i j => raw27182 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27182step0 raw27182; decide +kernel
      have hl : raw27182step0Labels = raw27182Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27182 raw27182Labels permutation173 permutation2
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw27183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27183step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27183 raw27183Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw27183 raw27183Labels = mixedMoment B raw27183step0 raw27183step0Labels := by
      have hz : ∀ j, raw27183 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27183step0 = (fun i j => raw27183 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27183step0 raw27183; decide +kernel
      have hl : raw27183step0Labels = raw27183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27183 raw27183Labels permutation265 hz
    mixedMoment B raw27183step0 raw27183step0Labels = mixedMoment B raw27183step1 raw27183step1Labels := by
      have ha : raw27183step1 = (fun i j => raw27183step0 (permutation43 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27183step1 raw27183step0; decide +kernel
      have hl : raw27183step1Labels = raw27183step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27183step0 raw27183step0Labels permutation43 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw27184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27184 raw27184Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw27184 raw27184Labels = mixedMoment B raw27184step0 raw27184step0Labels := by
      have hz : ∀ j, raw27184 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27184step0 = (fun i j => raw27184 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27184step0 raw27184; decide +kernel
      have hl : raw27184step0Labels = raw27184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27184 raw27184Labels permutation265 hz
    mixedMoment B raw27184step0 raw27184step0Labels = mixedMoment B raw27184step1 raw27184step1Labels := by
      have ha : raw27184step1 = (fun i j => raw27184step0 (permutation49 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27184step1 raw27184step0; decide +kernel
      have hl : raw27184step1Labels = raw27184step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27184step0 raw27184step0Labels permutation49 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw27185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27185step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27185 raw27185Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw27185 raw27185Labels = mixedMoment B raw27185step0 raw27185step0Labels := by
      have hz : ∀ j, raw27185 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27185step0 = (fun i j => raw27185 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27185step0 raw27185; decide +kernel
      have hl : raw27185step0Labels = raw27185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27185 raw27185Labels permutation590 hz
    mixedMoment B raw27185step0 raw27185step0Labels = mixedMoment B raw27185step1 raw27185step1Labels := by
      have hz : ∀ j, raw27185step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27185step1 = (fun i j => raw27185step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27185step1 raw27185step0; decide +kernel
      have hl : raw27185step1Labels = raw27185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27185step0 raw27185step0Labels permutation56 hz
    mixedMoment B raw27185step1 raw27185step1Labels = mixedMoment B raw27185step2 raw27185step2Labels := by
      have ha : raw27185step2 = (fun i j => raw27185step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27185step2 raw27185step1; decide +kernel
      have hl : raw27185step2Labels = raw27185step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27185step1 raw27185step1Labels permutation11 permutation2
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw27186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27186 raw27186Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw27186 raw27186Labels = mixedMoment B raw27186step0 raw27186step0Labels := by
      have hz : ∀ j, raw27186 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27186step0 = (fun i j => raw27186 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27186step0 raw27186; decide +kernel
      have hl : raw27186step0Labels = raw27186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27186 raw27186Labels permutation265 hz
    mixedMoment B raw27186step0 raw27186step0Labels = mixedMoment B raw27186step1 raw27186step1Labels := by
      have ha : raw27186step1 = (fun i j => raw27186step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27186step1 raw27186step0; decide +kernel
      have hl : raw27186step1Labels = raw27186step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27186step0 raw27186step0Labels permutation51 permutation2
    _ = mixedMoment B node4175 node4175Labels := by rfl

def raw27187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27187 raw27187Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw27187 raw27187Labels = mixedMoment B raw27187step0 raw27187step0Labels := by
      have ha : raw27187step0 = (fun i j => raw27187 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27187step0 raw27187; decide +kernel
      have hl : raw27187step0Labels = raw27187Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27187 raw27187Labels permutation171 permutation2
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw27188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27188 raw27188Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw27188 raw27188Labels = mixedMoment B raw27188step0 raw27188step0Labels := by
      have hz : ∀ j, raw27188 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27188step0 = (fun i j => raw27188 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27188step0 raw27188; decide +kernel
      have hl : raw27188step0Labels = raw27188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27188 raw27188Labels permutation265 hz
    mixedMoment B raw27188step0 raw27188step0Labels = mixedMoment B raw27188step1 raw27188step1Labels := by
      have ha : raw27188step1 = (fun i j => raw27188step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27188step1 raw27188step0; decide +kernel
      have hl : raw27188step1Labels = raw27188step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27188step0 raw27188step0Labels permutation37 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw27189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27189step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27189 raw27189Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw27189 raw27189Labels = mixedMoment B raw27189step0 raw27189step0Labels := by
      have hz : ∀ j, raw27189 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27189step0 = (fun i j => raw27189 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27189step0 raw27189; decide +kernel
      have hl : raw27189step0Labels = raw27189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27189 raw27189Labels permutation265 hz
    mixedMoment B raw27189step0 raw27189step0Labels = mixedMoment B raw27189step1 raw27189step1Labels := by
      have ha : raw27189step1 = (fun i j => raw27189step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27189step1 raw27189step0; decide +kernel
      have hl : raw27189step1Labels = raw27189step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27189step0 raw27189step0Labels permutation48 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw27190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27190 raw27190Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw27190 raw27190Labels = mixedMoment B raw27190step0 raw27190step0Labels := by
      have hz : ∀ j, raw27190 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27190step0 = (fun i j => raw27190 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27190step0 raw27190; decide +kernel
      have hl : raw27190step0Labels = raw27190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27190 raw27190Labels permutation590 hz
    mixedMoment B raw27190step0 raw27190step0Labels = mixedMoment B raw27190step1 raw27190step1Labels := by
      have hz : ∀ j, raw27190step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27190step1 = (fun i j => raw27190step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27190step1 raw27190step0; decide +kernel
      have hl : raw27190step1Labels = raw27190step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27190step0 raw27190step0Labels permutation56 hz
    mixedMoment B raw27190step1 raw27190step1Labels = mixedMoment B raw27190step2 raw27190step2Labels := by
      have ha : raw27190step2 = (fun i j => raw27190step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27190step2 raw27190step1; decide +kernel
      have hl : raw27190step2Labels = raw27190step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27190step1 raw27190step1Labels permutation9 permutation2
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw27191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27191step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27191 raw27191Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw27191 raw27191Labels = mixedMoment B raw27191step0 raw27191step0Labels := by
      have hz : ∀ j, raw27191 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27191step0 = (fun i j => raw27191 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27191step0 raw27191; decide +kernel
      have hl : raw27191step0Labels = raw27191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27191 raw27191Labels permutation265 hz
    mixedMoment B raw27191step0 raw27191step0Labels = mixedMoment B raw27191step1 raw27191step1Labels := by
      have ha : raw27191step1 = (fun i j => raw27191step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27191step1 raw27191step0; decide +kernel
      have hl : raw27191step1Labels = raw27191step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27191step0 raw27191step0Labels permutation50 permutation2
    _ = mixedMoment B node4175 node4175Labels := by rfl

def raw27192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27192 raw27192Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw27192 raw27192Labels = mixedMoment B raw27192step0 raw27192step0Labels := by
      have ha : raw27192step0 = (fun i j => raw27192 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27192step0 raw27192; decide +kernel
      have hl : raw27192step0Labels = raw27192Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27192 raw27192Labels permutation170 permutation2
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw27193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27193 raw27193Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw27193 raw27193Labels = mixedMoment B raw27193step0 raw27193step0Labels := by
      have hz : ∀ j, raw27193 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27193step0 = (fun i j => raw27193 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27193step0 raw27193; decide +kernel
      have hl : raw27193step0Labels = raw27193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27193 raw27193Labels permutation265 hz
    mixedMoment B raw27193step0 raw27193step0Labels = mixedMoment B raw27193step1 raw27193step1Labels := by
      have ha : raw27193step1 = (fun i j => raw27193step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27193step1 raw27193step0; decide +kernel
      have hl : raw27193step1Labels = raw27193step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27193step0 raw27193step0Labels permutation36 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw27194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27194 raw27194Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw27194 raw27194Labels = mixedMoment B raw27194step0 raw27194step0Labels := by
      have hz : ∀ j, raw27194 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27194step0 = (fun i j => raw27194 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27194step0 raw27194; decide +kernel
      have hl : raw27194step0Labels = raw27194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27194 raw27194Labels permutation265 hz
    mixedMoment B raw27194step0 raw27194step0Labels = mixedMoment B raw27194step1 raw27194step1Labels := by
      have ha : raw27194step1 = (fun i j => raw27194step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27194step1 raw27194step0; decide +kernel
      have hl : raw27194step1Labels = raw27194step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27194step0 raw27194step0Labels permutation42 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw27195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw27195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27195 raw27195Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw27195 raw27195Labels = mixedMoment B raw27195step0 raw27195step0Labels := by
      have hz : ∀ j, raw27195 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27195step0 = (fun i j => raw27195 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27195step0 raw27195; decide +kernel
      have hl : raw27195step0Labels = raw27195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27195 raw27195Labels permutation590 hz
    mixedMoment B raw27195step0 raw27195step0Labels = mixedMoment B raw27195step1 raw27195step1Labels := by
      have hz : ∀ j, raw27195step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27195step1 = (fun i j => raw27195step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27195step1 raw27195step0; decide +kernel
      have hl : raw27195step1Labels = raw27195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27195step0 raw27195step0Labels permutation56 hz
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw27196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27196 raw27196Labels = mixedMoment B node4182 node4182Labels := by
  calc
    mixedMoment B raw27196 raw27196Labels = mixedMoment B raw27196step0 raw27196step0Labels := by
      have hz : ∀ j, raw27196 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27196step0 = (fun i j => raw27196 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27196step0 raw27196; decide +kernel
      have hl : raw27196step0Labels = raw27196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27196 raw27196Labels permutation265 hz
    _ = mixedMoment B node4182 node4182Labels := by rfl

def raw27197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27197 raw27197Labels = mixedMoment B node4351 node4351Labels := by
  calc
    _ = mixedMoment B node4351 node4351Labels := by rfl

def raw27198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27198 raw27198Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw27198 raw27198Labels = mixedMoment B raw27198step0 raw27198step0Labels := by
      have hz : ∀ j, raw27198 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27198step0 = (fun i j => raw27198 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27198step0 raw27198; decide +kernel
      have hl : raw27198step0Labels = raw27198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27198 raw27198Labels permutation265 hz
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw27199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27199 raw27199Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw27199 raw27199Labels = mixedMoment B raw27199step0 raw27199step0Labels := by
      have hz : ∀ j, raw27199 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27199step0 = (fun i j => raw27199 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27199step0 raw27199; decide +kernel
      have hl : raw27199step0Labels = raw27199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27199 raw27199Labels permutation265 hz
    mixedMoment B raw27199step0 raw27199step0Labels = mixedMoment B raw27199step1 raw27199step1Labels := by
      have ha : raw27199step1 = (fun i j => raw27199step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27199step1 raw27199step0; decide +kernel
      have hl : raw27199step1Labels = raw27199step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27199step0 raw27199step0Labels permutation38 permutation2
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw27200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw27200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw27200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27200 raw27200Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw27200 raw27200Labels = mixedMoment B raw27200step0 raw27200step0Labels := by
      have hz : ∀ j, raw27200 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27200step0 = (fun i j => raw27200 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27200step0 raw27200; decide +kernel
      have hl : raw27200step0Labels = raw27200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27200 raw27200Labels permutation265 hz
    mixedMoment B raw27200step0 raw27200step0Labels = mixedMoment B raw27200step1 raw27200step1Labels := by
      have ha : raw27200step1 = (fun i j => raw27200step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27200step1 raw27200step0; decide +kernel
      have hl : raw27200step1Labels = raw27200step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27200step0 raw27200step0Labels permutation44 permutation2
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw27201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27201 raw27201Labels = mixedMoment B node995 node995Labels := by
  calc
    mixedMoment B raw27201 raw27201Labels = mixedMoment B raw27201step0 raw27201step0Labels := by
      have ha : raw27201step0 = (fun i j => raw27201 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27201step0 raw27201; decide +kernel
      have hl : raw27201step0Labels = raw27201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27201 raw27201Labels permutation169 permutation2
    _ = mixedMoment B node995 node995Labels := by rfl

def raw27202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27202 raw27202Labels = mixedMoment B node1940 node1940Labels := by
  calc
    mixedMoment B raw27202 raw27202Labels = mixedMoment B raw27202step0 raw27202step0Labels := by
      have ha : raw27202step0 = (fun i j => raw27202 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27202step0 raw27202; decide +kernel
      have hl : raw27202step0Labels = raw27202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27202 raw27202Labels permutation169 permutation2
    _ = mixedMoment B node1940 node1940Labels := by rfl

def raw27203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27203 raw27203Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw27203 raw27203Labels = mixedMoment B raw27203step0 raw27203step0Labels := by
      have ha : raw27203step0 = (fun i j => raw27203 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27203step0 raw27203; decide +kernel
      have hl : raw27203step0Labels = raw27203Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27203 raw27203Labels permutation155 permutation2
    _ = mixedMoment B node2219 node2219Labels := by rfl

def raw27204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27204 raw27204Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw27204 raw27204Labels = mixedMoment B raw27204step0 raw27204step0Labels := by
      have ha : raw27204step0 = (fun i j => raw27204 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27204step0 raw27204; decide +kernel
      have hl : raw27204step0Labels = raw27204Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27204 raw27204Labels permutation161 permutation2
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw27205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw27205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27205 raw27205Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27205 raw27205Labels = mixedMoment B raw27205step0 raw27205step0Labels := by
      have hz : ∀ j, raw27205 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27205step0 = (fun i j => raw27205 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27205step0 raw27205; decide +kernel
      have hl : raw27205step0Labels = raw27205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27205 raw27205Labels permutation520 hz
    mixedMoment B raw27205step0 raw27205step0Labels = mixedMoment B raw27205step1 raw27205step1Labels := by
      have ha : raw27205step1 = (fun i j => raw27205step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27205step1 raw27205step0; decide +kernel
      have hl : raw27205step1Labels = raw27205step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27205step0 raw27205step0Labels permutation37 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw27206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw27206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27206 raw27206Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27206 raw27206Labels = mixedMoment B raw27206step0 raw27206step0Labels := by
      have hz : ∀ j, raw27206 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27206step0 = (fun i j => raw27206 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27206step0 raw27206; decide +kernel
      have hl : raw27206step0Labels = raw27206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27206 raw27206Labels permutation590 hz
    mixedMoment B raw27206step0 raw27206step0Labels = mixedMoment B raw27206step1 raw27206step1Labels := by
      have ha : raw27206step1 = (fun i j => raw27206step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27206step1 raw27206step0; decide +kernel
      have hl : raw27206step1Labels = raw27206step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27206step0 raw27206step0Labels permutation37 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw27207 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1], ![0, 0], ![0, 0]]
def raw27207Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27207step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1], ![0, 0]]
def raw27207step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27207step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw27207step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27207step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw27207step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27207 raw27207Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw27207 raw27207Labels = mixedMoment B raw27207step0 raw27207step0Labels := by
      have hz : ∀ j, raw27207 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27207step0 = (fun i j => raw27207 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27207step0 raw27207; decide +kernel
      have hl : raw27207step0Labels = raw27207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27207 raw27207Labels permutation590 hz
    mixedMoment B raw27207step0 raw27207step0Labels = mixedMoment B raw27207step1 raw27207step1Labels := by
      have hz : ∀ j, raw27207step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw27207step1 = (fun i j => raw27207step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw27207step1 raw27207step0; decide +kernel
      have hl : raw27207step1Labels = raw27207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27207step0 raw27207step0Labels permutation128 hz
    mixedMoment B raw27207step1 raw27207step1Labels = mixedMoment B raw27207step2 raw27207step2Labels := by
      have ha : raw27207step2 = (fun i j => raw27207step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27207step2 raw27207step1; decide +kernel
      have hl : raw27207step2Labels = raw27207step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27207step1 raw27207step1Labels permutation9 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw27208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27208 raw27208Labels = mixedMoment B node996 node996Labels := by
  calc
    mixedMoment B raw27208 raw27208Labels = mixedMoment B raw27208step0 raw27208step0Labels := by
      have ha : raw27208step0 = (fun i j => raw27208 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27208step0 raw27208; decide +kernel
      have hl : raw27208step0Labels = raw27208Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27208 raw27208Labels permutation168 permutation2
    _ = mixedMoment B node996 node996Labels := by rfl

def raw27209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27209 raw27209Labels = mixedMoment B node1941 node1941Labels := by
  calc
    mixedMoment B raw27209 raw27209Labels = mixedMoment B raw27209step0 raw27209step0Labels := by
      have ha : raw27209step0 = (fun i j => raw27209 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27209step0 raw27209; decide +kernel
      have hl : raw27209step0Labels = raw27209Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27209 raw27209Labels permutation168 permutation2
    _ = mixedMoment B node1941 node1941Labels := by rfl

def raw27210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27210 raw27210Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw27210 raw27210Labels = mixedMoment B raw27210step0 raw27210step0Labels := by
      have ha : raw27210step0 = (fun i j => raw27210 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27210step0 raw27210; decide +kernel
      have hl : raw27210step0Labels = raw27210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27210 raw27210Labels permutation155 permutation2
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw27211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27211 raw27211Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw27211 raw27211Labels = mixedMoment B raw27211step0 raw27211step0Labels := by
      have ha : raw27211step0 = (fun i j => raw27211 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27211step0 raw27211; decide +kernel
      have hl : raw27211step0Labels = raw27211Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27211 raw27211Labels permutation161 permutation2
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw27212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0]]
def raw27212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw27212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27212 raw27212Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw27212 raw27212Labels = mixedMoment B raw27212step0 raw27212step0Labels := by
      have hz : ∀ j, raw27212 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27212step0 = (fun i j => raw27212 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27212step0 raw27212; decide +kernel
      have hl : raw27212step0Labels = raw27212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27212 raw27212Labels permutation520 hz
    mixedMoment B raw27212step0 raw27212step0Labels = mixedMoment B raw27212step1 raw27212step1Labels := by
      have ha : raw27212step1 = (fun i j => raw27212step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27212step1 raw27212step0; decide +kernel
      have hl : raw27212step1Labels = raw27212step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27212step0 raw27212step0Labels permutation36 permutation2
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw27213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0]]
def raw27213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw27213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27213 raw27213Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw27213 raw27213Labels = mixedMoment B raw27213step0 raw27213step0Labels := by
      have hz : ∀ j, raw27213 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27213step0 = (fun i j => raw27213 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27213step0 raw27213; decide +kernel
      have hl : raw27213step0Labels = raw27213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27213 raw27213Labels permutation590 hz
    mixedMoment B raw27213step0 raw27213step0Labels = mixedMoment B raw27213step1 raw27213step1Labels := by
      have ha : raw27213step1 = (fun i j => raw27213step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27213step1 raw27213step0; decide +kernel
      have hl : raw27213step1Labels = raw27213step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27213step0 raw27213step0Labels permutation36 permutation2
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw27214 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2], ![0, 0], ![0, 0]]
def raw27214Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27214step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2], ![0, 0]]
def raw27214step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27214step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw27214step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27214 raw27214Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw27214 raw27214Labels = mixedMoment B raw27214step0 raw27214step0Labels := by
      have hz : ∀ j, raw27214 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27214step0 = (fun i j => raw27214 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27214step0 raw27214; decide +kernel
      have hl : raw27214step0Labels = raw27214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27214 raw27214Labels permutation590 hz
    mixedMoment B raw27214step0 raw27214step0Labels = mixedMoment B raw27214step1 raw27214step1Labels := by
      have hz : ∀ j, raw27214step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw27214step1 = (fun i j => raw27214step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw27214step1 raw27214step0; decide +kernel
      have hl : raw27214step1Labels = raw27214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27214step0 raw27214step0Labels permutation128 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw27215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27215step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27215step0Labels : Fin 2 → Fin 3 := ![0, 2]

def raw27215step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27215step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27215 raw27215Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw27215 raw27215Labels = mixedMoment B raw27215step0 raw27215step0Labels := by
      have hz : ∀ i, raw27215 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw27215step0 = (fun i j => raw27215 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw27215step0 raw27215; decide +kernel
      have hl : raw27215step0Labels = (fun j => raw27215Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27215 raw27215Labels permutation4 hz
    mixedMoment B raw27215step0 raw27215step0Labels = mixedMoment B raw27215step1 raw27215step1Labels := by
      have ha : raw27215step1 = raw27215step0 := by apply Matrix.ext; unfold raw27215step1 raw27215step0; decide +kernel
      have hl : raw27215step0Labels = labelEmbedding2 ∘ raw27215step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27215step0 raw27215step0Labels raw27215step1Labels labelEmbedding2 hl
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw27216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27216step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27216step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27216step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27216step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27216 raw27216Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw27216 raw27216Labels = mixedMoment B raw27216step0 raw27216step0Labels := by
      have ha : raw27216step0 = (fun i j => raw27216 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27216step0 raw27216; decide +kernel
      have hl : raw27216step0Labels = raw27216Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27216 raw27216Labels permutation152 permutation7
    mixedMoment B raw27216step0 raw27216step0Labels = mixedMoment B raw27216step1 raw27216step1Labels := by
      have ha : raw27216step1 = -raw27216step0 := by apply Matrix.ext; change ∀ i j, raw27216step1 i j = -(raw27216step0 i j); unfold raw27216step1 raw27216step0; decide +kernel
      have hl : raw27216step1Labels = raw27216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27216step1 raw27216step1Labels = mixedMoment B raw27216step2 raw27216step2Labels := by
      have ha : raw27216step2 = raw27216step1 := by apply Matrix.ext; unfold raw27216step2 raw27216step1; decide +kernel
      have hl : raw27216step1Labels = labelEmbedding10 ∘ raw27216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27216step1 raw27216step1Labels raw27216step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw27217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27217step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27217step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27217step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27217step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27217 raw27217Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw27217 raw27217Labels = mixedMoment B raw27217step0 raw27217step0Labels := by
      have ha : raw27217step0 = (fun i j => raw27217 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27217step0 raw27217; decide +kernel
      have hl : raw27217step0Labels = raw27217Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27217 raw27217Labels permutation158 permutation7
    mixedMoment B raw27217step0 raw27217step0Labels = mixedMoment B raw27217step1 raw27217step1Labels := by
      have ha : raw27217step1 = -raw27217step0 := by apply Matrix.ext; change ∀ i j, raw27217step1 i j = -(raw27217step0 i j); unfold raw27217step1 raw27217step0; decide +kernel
      have hl : raw27217step1Labels = raw27217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27217step1 raw27217step1Labels = mixedMoment B raw27217step2 raw27217step2Labels := by
      have ha : raw27217step2 = raw27217step1 := by apply Matrix.ext; unfold raw27217step2 raw27217step1; decide +kernel
      have hl : raw27217step1Labels = labelEmbedding10 ∘ raw27217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27217step1 raw27217step1Labels raw27217step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw27218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw27218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27218step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27218step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27218step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27218step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27218 raw27218Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw27218 raw27218Labels = mixedMoment B raw27218step0 raw27218step0Labels := by
      have ha : raw27218step0 = (fun i j => raw27218 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27218step0 raw27218; decide +kernel
      have hl : raw27218step0Labels = raw27218Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27218 raw27218Labels permutation164 permutation7
    mixedMoment B raw27218step0 raw27218step0Labels = mixedMoment B raw27218step1 raw27218step1Labels := by
      have ha : raw27218step1 = -raw27218step0 := by apply Matrix.ext; change ∀ i j, raw27218step1 i j = -(raw27218step0 i j); unfold raw27218step1 raw27218step0; decide +kernel
      have hl : raw27218step1Labels = raw27218step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27218step1 raw27218step1Labels = mixedMoment B raw27218step2 raw27218step2Labels := by
      have ha : raw27218step2 = raw27218step1 := by apply Matrix.ext; unfold raw27218step2 raw27218step1; decide +kernel
      have hl : raw27218step1Labels = labelEmbedding10 ∘ raw27218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27218step1 raw27218step1Labels raw27218step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw27219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw27219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27219step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27219step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27219step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27219 raw27219Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw27219 raw27219Labels = mixedMoment B raw27219step0 raw27219step0Labels := by
      have ha : raw27219step0 = (fun i j => raw27219 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27219step0 raw27219; decide +kernel
      have hl : raw27219step0Labels = raw27219Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27219 raw27219Labels permutation170 permutation7
    mixedMoment B raw27219step0 raw27219step0Labels = mixedMoment B raw27219step1 raw27219step1Labels := by
      have ha : raw27219step1 = -raw27219step0 := by apply Matrix.ext; change ∀ i j, raw27219step1 i j = -(raw27219step0 i j); unfold raw27219step1 raw27219step0; decide +kernel
      have hl : raw27219step1Labels = raw27219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27219step1 raw27219step1Labels = mixedMoment B raw27219step2 raw27219step2Labels := by
      have ha : raw27219step2 = raw27219step1 := by apply Matrix.ext; unfold raw27219step2 raw27219step1; decide +kernel
      have hl : raw27219step1Labels = labelEmbedding10 ∘ raw27219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27219step1 raw27219step1Labels raw27219step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw27220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27220 raw27220Labels = mixedMoment B node4164 node4164Labels := by
  calc
    _ = mixedMoment B node4164 node4164Labels := by rfl

def raw27221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27221 raw27221Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27221 raw27221Labels = mixedMoment B raw27221step0 raw27221step0Labels := by
      have ha : raw27221step0 = (fun i j => raw27221 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27221step0 raw27221; decide +kernel
      have hl : raw27221step0Labels = raw27221Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27221 raw27221Labels permutation176 permutation2
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw27222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27222 raw27222Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27222 raw27222Labels = mixedMoment B raw27222step0 raw27222step0Labels := by
      have ha : raw27222step0 = (fun i j => raw27222 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27222step0 raw27222; decide +kernel
      have hl : raw27222step0Labels = raw27222Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27222 raw27222Labels permutation200 permutation2
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw27223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw27223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27223 raw27223Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27223 raw27223Labels = mixedMoment B raw27223step0 raw27223step0Labels := by
      have ha : raw27223step0 = (fun i j => raw27223 (permutation224 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27223step0 raw27223; decide +kernel
      have hl : raw27223step0Labels = raw27223Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27223 raw27223Labels permutation224 permutation2
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw27224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw27224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27224 raw27224Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27224 raw27224Labels = mixedMoment B raw27224step0 raw27224step0Labels := by
      have ha : raw27224step0 = (fun i j => raw27224 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27224step0 raw27224; decide +kernel
      have hl : raw27224step0Labels = raw27224Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27224 raw27224Labels permutation246 permutation2
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw27225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27225 raw27225Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw27225 raw27225Labels = mixedMoment B raw27225step0 raw27225step0Labels := by
      have ha : raw27225step0 = (fun i j => raw27225 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27225step0 raw27225; decide +kernel
      have hl : raw27225step0Labels = raw27225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27225 raw27225Labels permutation161 permutation2
    _ = mixedMoment B node4143 node4143Labels := by rfl

def raw27226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27226 raw27226Labels = mixedMoment B node4306 node4306Labels := by
  calc
    mixedMoment B raw27226 raw27226Labels = mixedMoment B raw27226step0 raw27226step0Labels := by
      have ha : raw27226step0 = (fun i j => raw27226 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27226step0 raw27226; decide +kernel
      have hl : raw27226step0Labels = raw27226Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27226 raw27226Labels permutation161 permutation2
    _ = mixedMoment B node4306 node4306Labels := by rfl

def raw27227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27227 raw27227Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27227 raw27227Labels = mixedMoment B raw27227step0 raw27227step0Labels := by
      have ha : raw27227step0 = (fun i j => raw27227 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27227step0 raw27227; decide +kernel
      have hl : raw27227step0Labels = raw27227Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27227 raw27227Labels permutation161 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw27228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27228 raw27228Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27228 raw27228Labels = mixedMoment B raw27228step0 raw27228step0Labels := by
      have ha : raw27228step0 = (fun i j => raw27228 (permutation167 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27228step0 raw27228; decide +kernel
      have hl : raw27228step0Labels = raw27228Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27228 raw27228Labels permutation167 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw27229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27229 raw27229Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27229 raw27229Labels = mixedMoment B raw27229step0 raw27229step0Labels := by
      have ha : raw27229step0 = (fun i j => raw27229 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27229step0 raw27229; decide +kernel
      have hl : raw27229step0Labels = raw27229Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27229 raw27229Labels permutation173 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27230 raw27230Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw27230 raw27230Labels = mixedMoment B raw27230step0 raw27230step0Labels := by
      have ha : raw27230step0 = (fun i j => raw27230 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27230step0 raw27230; decide +kernel
      have hl : raw27230step0Labels = raw27230Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27230 raw27230Labels permutation155 permutation2
    _ = mixedMoment B node4143 node4143Labels := by rfl

def raw27231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27231 raw27231Labels = mixedMoment B node4306 node4306Labels := by
  calc
    mixedMoment B raw27231 raw27231Labels = mixedMoment B raw27231step0 raw27231step0Labels := by
      have ha : raw27231step0 = (fun i j => raw27231 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27231step0 raw27231; decide +kernel
      have hl : raw27231step0Labels = raw27231Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27231 raw27231Labels permutation155 permutation2
    _ = mixedMoment B node4306 node4306Labels := by rfl

def raw27232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27232 raw27232Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27232 raw27232Labels = mixedMoment B raw27232step0 raw27232step0Labels := by
      have ha : raw27232step0 = (fun i j => raw27232 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27232step0 raw27232; decide +kernel
      have hl : raw27232step0Labels = raw27232Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27232 raw27232Labels permutation155 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw27233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27233 raw27233Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27233 raw27233Labels = mixedMoment B raw27233step0 raw27233step0Labels := by
      have ha : raw27233step0 = (fun i j => raw27233 (permutation165 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27233step0 raw27233; decide +kernel
      have hl : raw27233step0Labels = raw27233Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27233 raw27233Labels permutation165 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw27234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27234 raw27234Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27234 raw27234Labels = mixedMoment B raw27234step0 raw27234step0Labels := by
      have ha : raw27234step0 = (fun i j => raw27234 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27234step0 raw27234; decide +kernel
      have hl : raw27234step0Labels = raw27234Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27234 raw27234Labels permutation171 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27235 raw27235Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw27235 raw27235Labels = mixedMoment B raw27235step0 raw27235step0Labels := by
      have ha : raw27235step0 = (fun i j => raw27235 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27235step0 raw27235; decide +kernel
      have hl : raw27235step0Labels = raw27235Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27235 raw27235Labels permutation153 permutation2
    _ = mixedMoment B node4143 node4143Labels := by rfl

def raw27236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27236 raw27236Labels = mixedMoment B node4306 node4306Labels := by
  calc
    mixedMoment B raw27236 raw27236Labels = mixedMoment B raw27236step0 raw27236step0Labels := by
      have ha : raw27236step0 = (fun i j => raw27236 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27236step0 raw27236; decide +kernel
      have hl : raw27236step0Labels = raw27236Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27236 raw27236Labels permutation153 permutation2
    _ = mixedMoment B node4306 node4306Labels := by rfl

def raw27237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27237 raw27237Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27237 raw27237Labels = mixedMoment B raw27237step0 raw27237step0Labels := by
      have ha : raw27237step0 = (fun i j => raw27237 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27237step0 raw27237; decide +kernel
      have hl : raw27237step0Labels = raw27237Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27237 raw27237Labels permutation153 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27238 raw27238Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27238 raw27238Labels = mixedMoment B raw27238step0 raw27238step0Labels := by
      have ha : raw27238step0 = (fun i j => raw27238 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27238step0 raw27238; decide +kernel
      have hl : raw27238step0Labels = raw27238Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27238 raw27238Labels permutation159 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw27239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27239 raw27239Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27239 raw27239Labels = mixedMoment B raw27239step0 raw27239step0Labels := by
      have ha : raw27239step0 = (fun i j => raw27239 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27239step0 raw27239; decide +kernel
      have hl : raw27239step0Labels = raw27239Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27239 raw27239Labels permutation170 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27240 raw27240Labels = mixedMoment B node4143 node4143Labels := by
  calc
    _ = mixedMoment B node4143 node4143Labels := by rfl

def raw27241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27241 raw27241Labels = mixedMoment B node4306 node4306Labels := by
  calc
    _ = mixedMoment B node4306 node4306Labels := by rfl

def raw27242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27242 raw27242Labels = mixedMoment B node4399 node4399Labels := by
  calc
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27243step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27243 raw27243Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27243 raw27243Labels = mixedMoment B raw27243step0 raw27243step0Labels := by
      have ha : raw27243step0 = (fun i j => raw27243 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27243step0 raw27243; decide +kernel
      have hl : raw27243step0Labels = raw27243Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27243 raw27243Labels permutation158 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw27244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27244 raw27244Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27244 raw27244Labels = mixedMoment B raw27244step0 raw27244step0Labels := by
      have ha : raw27244step0 = (fun i j => raw27244 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27244step0 raw27244; decide +kernel
      have hl : raw27244step0Labels = raw27244Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27244 raw27244Labels permutation164 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw27245 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw27245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27245step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27245 raw27245Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw27245 raw27245Labels = mixedMoment B raw27245step0 raw27245step0Labels := by
      have ha : raw27245step0 = (fun i j => raw27245 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27245step0 raw27245; decide +kernel
      have hl : raw27245step0Labels = raw27245Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27245 raw27245Labels permutation170 permutation6
    mixedMoment B raw27245step0 raw27245step0Labels = mixedMoment B raw27245step1 raw27245step1Labels := by
      have ha : raw27245step1 = raw27245step0 := by apply Matrix.ext; unfold raw27245step1 raw27245step0; decide +kernel
      have hl : raw27245step0Labels = labelEmbedding9 ∘ raw27245step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27245step0 raw27245step0Labels raw27245step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw27246 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw27246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw27246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27246step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw27246step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw27246step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27246step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw27246step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27246step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27246 raw27246Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw27246 raw27246Labels = mixedMoment B raw27246step0 raw27246step0Labels := by
      have hz : ∀ j, raw27246 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27246step0 = (fun i j => raw27246 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27246step0 raw27246; decide +kernel
      have hl : raw27246step0Labels = raw27246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27246 raw27246Labels permutation265 hz
    mixedMoment B raw27246step0 raw27246step0Labels = mixedMoment B raw27246step1 raw27246step1Labels := by
      have hz : ∀ i, raw27246step0 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw27246step1 = (fun i j => raw27246step0 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw27246step1 raw27246step0; decide +kernel
      have hl : raw27246step1Labels = (fun j => raw27246step0Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27246step0 raw27246step0Labels permutation2 hz
    mixedMoment B raw27246step1 raw27246step1Labels = mixedMoment B raw27246step2 raw27246step2Labels := by
      have ha : raw27246step2 = -raw27246step1 := by apply Matrix.ext; change ∀ i j, raw27246step2 i j = -(raw27246step1 i j); unfold raw27246step2 raw27246step1; decide +kernel
      have hl : raw27246step2Labels = raw27246step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27246step2 raw27246step2Labels = mixedMoment B raw27246step3 raw27246step3Labels := by
      have ha : raw27246step3 = raw27246step2 := by apply Matrix.ext; unfold raw27246step3 raw27246step2; decide +kernel
      have hl : raw27246step2Labels = labelEmbedding3 ∘ raw27246step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27246step2 raw27246step2Labels raw27246step3Labels labelEmbedding3 hl
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw27247 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw27247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27247step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27247step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27247step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27247 raw27247Labels = mixedMoment B node4216 node4216Labels := by
  calc
    mixedMoment B raw27247 raw27247Labels = mixedMoment B raw27247step0 raw27247step0Labels := by
      have ha : raw27247step0 = (fun i j => raw27247 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27247step0 raw27247; decide +kernel
      have hl : raw27247step0Labels = raw27247Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27247 raw27247Labels permutation161 permutation4
    mixedMoment B raw27247step0 raw27247step0Labels = mixedMoment B raw27247step1 raw27247step1Labels := by
      have ha : raw27247step1 = -raw27247step0 := by apply Matrix.ext; change ∀ i j, raw27247step1 i j = -(raw27247step0 i j); unfold raw27247step1 raw27247step0; decide +kernel
      have hl : raw27247step1Labels = raw27247step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27247step1 raw27247step1Labels = mixedMoment B raw27247step2 raw27247step2Labels := by
      have ha : raw27247step2 = raw27247step1 := by apply Matrix.ext; unfold raw27247step2 raw27247step1; decide +kernel
      have hl : raw27247step1Labels = labelEmbedding7 ∘ raw27247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27247step1 raw27247step1Labels raw27247step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4216 node4216Labels := by rfl

def raw27248 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw27248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27248step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27248 raw27248Labels = mixedMoment B node4379 node4379Labels := by
  calc
    mixedMoment B raw27248 raw27248Labels = mixedMoment B raw27248step0 raw27248step0Labels := by
      have ha : raw27248step0 = (fun i j => raw27248 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27248step0 raw27248; decide +kernel
      have hl : raw27248step0Labels = raw27248Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27248 raw27248Labels permutation161 permutation6
    mixedMoment B raw27248step0 raw27248step0Labels = mixedMoment B raw27248step1 raw27248step1Labels := by
      have ha : raw27248step1 = raw27248step0 := by apply Matrix.ext; unfold raw27248step1 raw27248step0; decide +kernel
      have hl : raw27248step0Labels = labelEmbedding9 ∘ raw27248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27248step0 raw27248step0Labels raw27248step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4379 node4379Labels := by rfl

def raw27249 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw27249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27249step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27249 raw27249Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw27249 raw27249Labels = mixedMoment B raw27249step0 raw27249step0Labels := by
      have ha : raw27249step0 = (fun i j => raw27249 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27249step0 raw27249; decide +kernel
      have hl : raw27249step0Labels = raw27249Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27249 raw27249Labels permutation161 permutation6
    mixedMoment B raw27249step0 raw27249step0Labels = mixedMoment B raw27249step1 raw27249step1Labels := by
      have ha : raw27249step1 = raw27249step0 := by apply Matrix.ext; unfold raw27249step1 raw27249step0; decide +kernel
      have hl : raw27249step0Labels = labelEmbedding9 ∘ raw27249step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27249step0 raw27249step0Labels raw27249step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw27250 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw27250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27250step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27250step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27250step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27250 raw27250Labels = mixedMoment B node4216 node4216Labels := by
  calc
    mixedMoment B raw27250 raw27250Labels = mixedMoment B raw27250step0 raw27250step0Labels := by
      have ha : raw27250step0 = (fun i j => raw27250 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27250step0 raw27250; decide +kernel
      have hl : raw27250step0Labels = raw27250Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27250 raw27250Labels permutation155 permutation4
    mixedMoment B raw27250step0 raw27250step0Labels = mixedMoment B raw27250step1 raw27250step1Labels := by
      have ha : raw27250step1 = -raw27250step0 := by apply Matrix.ext; change ∀ i j, raw27250step1 i j = -(raw27250step0 i j); unfold raw27250step1 raw27250step0; decide +kernel
      have hl : raw27250step1Labels = raw27250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27250step1 raw27250step1Labels = mixedMoment B raw27250step2 raw27250step2Labels := by
      have ha : raw27250step2 = raw27250step1 := by apply Matrix.ext; unfold raw27250step2 raw27250step1; decide +kernel
      have hl : raw27250step1Labels = labelEmbedding7 ∘ raw27250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27250step1 raw27250step1Labels raw27250step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4216 node4216Labels := by rfl

def raw27251 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw27251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27251step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27251 raw27251Labels = mixedMoment B node4379 node4379Labels := by
  calc
    mixedMoment B raw27251 raw27251Labels = mixedMoment B raw27251step0 raw27251step0Labels := by
      have ha : raw27251step0 = (fun i j => raw27251 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27251step0 raw27251; decide +kernel
      have hl : raw27251step0Labels = raw27251Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27251 raw27251Labels permutation155 permutation6
    mixedMoment B raw27251step0 raw27251step0Labels = mixedMoment B raw27251step1 raw27251step1Labels := by
      have ha : raw27251step1 = raw27251step0 := by apply Matrix.ext; unfold raw27251step1 raw27251step0; decide +kernel
      have hl : raw27251step0Labels = labelEmbedding9 ∘ raw27251step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27251step0 raw27251step0Labels raw27251step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4379 node4379Labels := by rfl

def raw27252 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw27252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27252step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27252 raw27252Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw27252 raw27252Labels = mixedMoment B raw27252step0 raw27252step0Labels := by
      have ha : raw27252step0 = (fun i j => raw27252 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27252step0 raw27252; decide +kernel
      have hl : raw27252step0Labels = raw27252Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27252 raw27252Labels permutation155 permutation6
    mixedMoment B raw27252step0 raw27252step0Labels = mixedMoment B raw27252step1 raw27252step1Labels := by
      have ha : raw27252step1 = raw27252step0 := by apply Matrix.ext; unfold raw27252step1 raw27252step0; decide +kernel
      have hl : raw27252step0Labels = labelEmbedding9 ∘ raw27252step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27252step0 raw27252step0Labels raw27252step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw27253 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27253step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27253 raw27253Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw27253 raw27253Labels = mixedMoment B raw27253step0 raw27253step0Labels := by
      have ha : raw27253step0 = (fun i j => raw27253 (permutation165 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27253step0 raw27253; decide +kernel
      have hl : raw27253step0Labels = raw27253Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27253 raw27253Labels permutation165 permutation6
    mixedMoment B raw27253step0 raw27253step0Labels = mixedMoment B raw27253step1 raw27253step1Labels := by
      have ha : raw27253step1 = raw27253step0 := by apply Matrix.ext; unfold raw27253step1 raw27253step0; decide +kernel
      have hl : raw27253step0Labels = labelEmbedding9 ∘ raw27253step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27253step0 raw27253step0Labels raw27253step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw27254 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw27254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27254step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27254step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27254step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27254 raw27254Labels = mixedMoment B node4216 node4216Labels := by
  calc
    mixedMoment B raw27254 raw27254Labels = mixedMoment B raw27254step0 raw27254step0Labels := by
      have ha : raw27254step0 = (fun i j => raw27254 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27254step0 raw27254; decide +kernel
      have hl : raw27254step0Labels = raw27254Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27254 raw27254Labels permutation153 permutation4
    mixedMoment B raw27254step0 raw27254step0Labels = mixedMoment B raw27254step1 raw27254step1Labels := by
      have ha : raw27254step1 = -raw27254step0 := by apply Matrix.ext; change ∀ i j, raw27254step1 i j = -(raw27254step0 i j); unfold raw27254step1 raw27254step0; decide +kernel
      have hl : raw27254step1Labels = raw27254step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27254step1 raw27254step1Labels = mixedMoment B raw27254step2 raw27254step2Labels := by
      have ha : raw27254step2 = raw27254step1 := by apply Matrix.ext; unfold raw27254step2 raw27254step1; decide +kernel
      have hl : raw27254step1Labels = labelEmbedding7 ∘ raw27254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27254step1 raw27254step1Labels raw27254step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4216 node4216Labels := by rfl

def raw27255 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw27255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27255step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27255 raw27255Labels = mixedMoment B node4379 node4379Labels := by
  calc
    mixedMoment B raw27255 raw27255Labels = mixedMoment B raw27255step0 raw27255step0Labels := by
      have ha : raw27255step0 = (fun i j => raw27255 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27255step0 raw27255; decide +kernel
      have hl : raw27255step0Labels = raw27255Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27255 raw27255Labels permutation153 permutation6
    mixedMoment B raw27255step0 raw27255step0Labels = mixedMoment B raw27255step1 raw27255step1Labels := by
      have ha : raw27255step1 = raw27255step0 := by apply Matrix.ext; unfold raw27255step1 raw27255step0; decide +kernel
      have hl : raw27255step0Labels = labelEmbedding9 ∘ raw27255step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27255step0 raw27255step0Labels raw27255step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4379 node4379Labels := by rfl

def raw27256 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw27256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27256step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27256 raw27256Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw27256 raw27256Labels = mixedMoment B raw27256step0 raw27256step0Labels := by
      have ha : raw27256step0 = (fun i j => raw27256 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27256step0 raw27256; decide +kernel
      have hl : raw27256step0Labels = raw27256Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27256 raw27256Labels permutation153 permutation6
    mixedMoment B raw27256step0 raw27256step0Labels = mixedMoment B raw27256step1 raw27256step1Labels := by
      have ha : raw27256step1 = raw27256step0 := by apply Matrix.ext; unfold raw27256step1 raw27256step0; decide +kernel
      have hl : raw27256step0Labels = labelEmbedding9 ∘ raw27256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27256step0 raw27256step0Labels raw27256step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw27257 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw27257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27257step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27257 raw27257Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw27257 raw27257Labels = mixedMoment B raw27257step0 raw27257step0Labels := by
      have ha : raw27257step0 = (fun i j => raw27257 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27257step0 raw27257; decide +kernel
      have hl : raw27257step0Labels = raw27257Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27257 raw27257Labels permutation159 permutation6
    mixedMoment B raw27257step0 raw27257step0Labels = mixedMoment B raw27257step1 raw27257step1Labels := by
      have ha : raw27257step1 = raw27257step0 := by apply Matrix.ext; unfold raw27257step1 raw27257step0; decide +kernel
      have hl : raw27257step0Labels = labelEmbedding9 ∘ raw27257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27257step0 raw27257step0Labels raw27257step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw27258 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw27258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27258step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27258step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27258 raw27258Labels = mixedMoment B node4216 node4216Labels := by
  calc
    mixedMoment B raw27258 raw27258Labels = mixedMoment B raw27258step0 raw27258step0Labels := by
      have ha : raw27258step0 = (fun i j => raw27258 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27258step0 raw27258; decide +kernel
      have hl : raw27258step0Labels = raw27258Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27258 raw27258Labels permutation152 permutation4
    mixedMoment B raw27258step0 raw27258step0Labels = mixedMoment B raw27258step1 raw27258step1Labels := by
      have ha : raw27258step1 = -raw27258step0 := by apply Matrix.ext; change ∀ i j, raw27258step1 i j = -(raw27258step0 i j); unfold raw27258step1 raw27258step0; decide +kernel
      have hl : raw27258step1Labels = raw27258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27258step1 raw27258step1Labels = mixedMoment B raw27258step2 raw27258step2Labels := by
      have ha : raw27258step2 = raw27258step1 := by apply Matrix.ext; unfold raw27258step2 raw27258step1; decide +kernel
      have hl : raw27258step1Labels = labelEmbedding7 ∘ raw27258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27258step1 raw27258step1Labels raw27258step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4216 node4216Labels := by rfl

def raw27259 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw27259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27259step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27259 raw27259Labels = mixedMoment B node4379 node4379Labels := by
  calc
    mixedMoment B raw27259 raw27259Labels = mixedMoment B raw27259step0 raw27259step0Labels := by
      have ha : raw27259step0 = (fun i j => raw27259 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27259step0 raw27259; decide +kernel
      have hl : raw27259step0Labels = raw27259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27259 raw27259Labels permutation152 permutation6
    mixedMoment B raw27259step0 raw27259step0Labels = mixedMoment B raw27259step1 raw27259step1Labels := by
      have ha : raw27259step1 = raw27259step0 := by apply Matrix.ext; unfold raw27259step1 raw27259step0; decide +kernel
      have hl : raw27259step0Labels = labelEmbedding9 ∘ raw27259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27259step0 raw27259step0Labels raw27259step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4379 node4379Labels := by rfl

def raw27260 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw27260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27260step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27260 raw27260Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw27260 raw27260Labels = mixedMoment B raw27260step0 raw27260step0Labels := by
      have ha : raw27260step0 = (fun i j => raw27260 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27260step0 raw27260; decide +kernel
      have hl : raw27260step0Labels = raw27260Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27260 raw27260Labels permutation152 permutation6
    mixedMoment B raw27260step0 raw27260step0Labels = mixedMoment B raw27260step1 raw27260step1Labels := by
      have ha : raw27260step1 = raw27260step0 := by apply Matrix.ext; unfold raw27260step1 raw27260step0; decide +kernel
      have hl : raw27260step0Labels = labelEmbedding9 ∘ raw27260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27260step0 raw27260step0Labels raw27260step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw27261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw27261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27261step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27261 raw27261Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw27261 raw27261Labels = mixedMoment B raw27261step0 raw27261step0Labels := by
      have ha : raw27261step0 = (fun i j => raw27261 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27261step0 raw27261; decide +kernel
      have hl : raw27261step0Labels = raw27261Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27261 raw27261Labels permutation158 permutation6
    mixedMoment B raw27261step0 raw27261step0Labels = mixedMoment B raw27261step1 raw27261step1Labels := by
      have ha : raw27261step1 = raw27261step0 := by apply Matrix.ext; unfold raw27261step1 raw27261step0; decide +kernel
      have hl : raw27261step0Labels = labelEmbedding9 ∘ raw27261step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27261step0 raw27261step0Labels raw27261step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw27262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw27262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27262step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27262 raw27262Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw27262 raw27262Labels = mixedMoment B raw27262step0 raw27262step0Labels := by
      have ha : raw27262step0 = (fun i j => raw27262 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27262step0 raw27262; decide +kernel
      have hl : raw27262step0Labels = raw27262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27262 raw27262Labels permutation164 permutation6
    mixedMoment B raw27262step0 raw27262step0Labels = mixedMoment B raw27262step1 raw27262step1Labels := by
      have ha : raw27262step1 = raw27262step0 := by apply Matrix.ext; unfold raw27262step1 raw27262step0; decide +kernel
      have hl : raw27262step0Labels = labelEmbedding9 ∘ raw27262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27262step0 raw27262step0Labels raw27262step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw27263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27263step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27263step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27263step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27263step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27263 raw27263Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27263 raw27263Labels = mixedMoment B raw27263step0 raw27263step0Labels := by
      have ha : raw27263step0 = (fun i j => raw27263 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27263step0 raw27263; decide +kernel
      have hl : raw27263step0Labels = raw27263Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27263 raw27263Labels permutation246 permutation7
    mixedMoment B raw27263step0 raw27263step0Labels = mixedMoment B raw27263step1 raw27263step1Labels := by
      have ha : raw27263step1 = -raw27263step0 := by apply Matrix.ext; change ∀ i j, raw27263step1 i j = -(raw27263step0 i j); unfold raw27263step1 raw27263step0; decide +kernel
      have hl : raw27263step1Labels = raw27263step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27263step1 raw27263step1Labels = mixedMoment B raw27263step2 raw27263step2Labels := by
      have ha : raw27263step2 = raw27263step1 := by apply Matrix.ext; unfold raw27263step2 raw27263step1; decide +kernel
      have hl : raw27263step1Labels = labelEmbedding10 ∘ raw27263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27263step1 raw27263step1Labels raw27263step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
