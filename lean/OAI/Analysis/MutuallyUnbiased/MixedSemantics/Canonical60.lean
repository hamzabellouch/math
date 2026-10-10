import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7680Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7680step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7680step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw7680step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7680step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7680step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7680step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7680step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7680 raw7680Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw7680 raw7680Labels = mixedMoment B raw7680step0 raw7680step0Labels := by
      have hz : ∀ j, raw7680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7680step0 = (fun i j => raw7680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7680step0 raw7680; decide +kernel
      have hl : raw7680step0Labels = raw7680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7680 raw7680Labels permutation434 hz
    mixedMoment B raw7680step0 raw7680step0Labels = mixedMoment B raw7680step1 raw7680step1Labels := by
      have hz : ∀ j, raw7680step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7680step1 = (fun i j => raw7680step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7680step1 raw7680step0; decide +kernel
      have hl : raw7680step1Labels = raw7680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7680step0 raw7680step0Labels permutation80 hz
    mixedMoment B raw7680step1 raw7680step1Labels = mixedMoment B raw7680step2 raw7680step2Labels := by
      have ha : raw7680step2 = (fun i j => raw7680step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7680step2 raw7680step1; decide +kernel
      have hl : raw7680step2Labels = raw7680step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7680step1 raw7680step1Labels permutation12 permutation5
    mixedMoment B raw7680step2 raw7680step2Labels = mixedMoment B raw7680step3 raw7680step3Labels := by
      have ha : raw7680step3 = -raw7680step2 := by apply Matrix.ext; change ∀ i j, raw7680step3 i j = -(raw7680step2 i j); unfold raw7680step3 raw7680step2; decide +kernel
      have hl : raw7680step3Labels = raw7680step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7680step3 raw7680step3Labels = mixedMoment B raw7680step4 raw7680step4Labels := by
      have ha : raw7680step4 = raw7680step3 := by apply Matrix.ext; unfold raw7680step4 raw7680step3; decide +kernel
      have hl : raw7680step3Labels = labelEmbedding1 ∘ raw7680step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7680step3 raw7680step3Labels raw7680step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw7681 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7681Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7681step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7681step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7681step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7681 raw7681Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw7681 raw7681Labels = mixedMoment B raw7681step0 raw7681step0Labels := by
      have hz : ∀ j, raw7681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7681step0 = (fun i j => raw7681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7681step0 raw7681; decide +kernel
      have hl : raw7681step0Labels = raw7681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7681 raw7681Labels permutation434 hz
    mixedMoment B raw7681step0 raw7681step0Labels = mixedMoment B raw7681step1 raw7681step1Labels := by
      have ha : raw7681step1 = (fun i j => raw7681step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7681step1 raw7681step0; decide +kernel
      have hl : raw7681step1Labels = raw7681step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7681step0 raw7681step0Labels permutation32 permutation7
    mixedMoment B raw7681step1 raw7681step1Labels = mixedMoment B raw7681step2 raw7681step2Labels := by
      have ha : raw7681step2 = raw7681step1 := by apply Matrix.ext; unfold raw7681step2 raw7681step1; decide +kernel
      have hl : raw7681step1Labels = labelEmbedding1 ∘ raw7681step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7681step1 raw7681step1Labels raw7681step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw7682 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7682Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7682step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7682step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7682 raw7682Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw7682 raw7682Labels = mixedMoment B raw7682step0 raw7682step0Labels := by
      have hz : ∀ j, raw7682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7682step0 = (fun i j => raw7682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7682step0 raw7682; decide +kernel
      have hl : raw7682step0Labels = raw7682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7682 raw7682Labels permutation346 hz
    mixedMoment B raw7682step0 raw7682step0Labels = mixedMoment B raw7682step1 raw7682step1Labels := by
      have ha : raw7682step1 = (fun i j => raw7682step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7682step1 raw7682step0; decide +kernel
      have hl : raw7682step1Labels = raw7682step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7682step0 raw7682step0Labels permutation32 permutation7
    mixedMoment B raw7682step1 raw7682step1Labels = mixedMoment B raw7682step2 raw7682step2Labels := by
      have ha : raw7682step2 = raw7682step1 := by apply Matrix.ext; unfold raw7682step2 raw7682step1; decide +kernel
      have hl : raw7682step1Labels = labelEmbedding1 ∘ raw7682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7682step1 raw7682step1Labels raw7682step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw7683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7683Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7683step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7683step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7683step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7683step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7683 raw7683Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw7683 raw7683Labels = mixedMoment B raw7683step0 raw7683step0Labels := by
      have hz : ∀ j, raw7683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7683step0 = (fun i j => raw7683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7683step0 raw7683; decide +kernel
      have hl : raw7683step0Labels = raw7683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7683 raw7683Labels permutation434 hz
    mixedMoment B raw7683step0 raw7683step0Labels = mixedMoment B raw7683step1 raw7683step1Labels := by
      have hz : ∀ j, raw7683step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7683step1 = (fun i j => raw7683step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7683step1 raw7683step0; decide +kernel
      have hl : raw7683step1Labels = raw7683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7683step0 raw7683step0Labels permutation80 hz
    mixedMoment B raw7683step1 raw7683step1Labels = mixedMoment B raw7683step2 raw7683step2Labels := by
      have ha : raw7683step2 = (fun i j => raw7683step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7683step2 raw7683step1; decide +kernel
      have hl : raw7683step2Labels = raw7683step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7683step1 raw7683step1Labels permutation8 permutation7
    mixedMoment B raw7683step2 raw7683step2Labels = mixedMoment B raw7683step3 raw7683step3Labels := by
      have ha : raw7683step3 = raw7683step2 := by apply Matrix.ext; unfold raw7683step3 raw7683step2; decide +kernel
      have hl : raw7683step2Labels = labelEmbedding1 ∘ raw7683step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7683step2 raw7683step2Labels raw7683step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw7684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7684Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7684step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7684step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7684step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7684step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7684 raw7684Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw7684 raw7684Labels = mixedMoment B raw7684step0 raw7684step0Labels := by
      have hz : ∀ j, raw7684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7684step0 = (fun i j => raw7684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7684step0 raw7684; decide +kernel
      have hl : raw7684step0Labels = raw7684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7684 raw7684Labels permutation434 hz
    mixedMoment B raw7684step0 raw7684step0Labels = mixedMoment B raw7684step1 raw7684step1Labels := by
      have hz : ∀ j, raw7684step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7684step1 = (fun i j => raw7684step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7684step1 raw7684step0; decide +kernel
      have hl : raw7684step1Labels = raw7684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7684step0 raw7684step0Labels permutation80 hz
    mixedMoment B raw7684step1 raw7684step1Labels = mixedMoment B raw7684step2 raw7684step2Labels := by
      have ha : raw7684step2 = (fun i j => raw7684step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7684step2 raw7684step1; decide +kernel
      have hl : raw7684step2Labels = raw7684step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7684step1 raw7684step1Labels permutation8 permutation7
    mixedMoment B raw7684step2 raw7684step2Labels = mixedMoment B raw7684step3 raw7684step3Labels := by
      have ha : raw7684step3 = raw7684step2 := by apply Matrix.ext; unfold raw7684step3 raw7684step2; decide +kernel
      have hl : raw7684step2Labels = labelEmbedding1 ∘ raw7684step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7684step2 raw7684step2Labels raw7684step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw7685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7685Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7685step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7685step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw7685step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7685step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7685step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7685step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7685 raw7685Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw7685 raw7685Labels = mixedMoment B raw7685step0 raw7685step0Labels := by
      have hz : ∀ j, raw7685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7685step0 = (fun i j => raw7685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7685step0 raw7685; decide +kernel
      have hl : raw7685step0Labels = raw7685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7685 raw7685Labels permutation434 hz
    mixedMoment B raw7685step0 raw7685step0Labels = mixedMoment B raw7685step1 raw7685step1Labels := by
      have hz : ∀ j, raw7685step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7685step1 = (fun i j => raw7685step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7685step1 raw7685step0; decide +kernel
      have hl : raw7685step1Labels = raw7685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7685step0 raw7685step0Labels permutation56 hz
    mixedMoment B raw7685step1 raw7685step1Labels = mixedMoment B raw7685step2 raw7685step2Labels := by
      have ha : raw7685step2 = (fun i j => raw7685step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7685step2 raw7685step1; decide +kernel
      have hl : raw7685step2Labels = raw7685step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7685step1 raw7685step1Labels permutation12 permutation5
    mixedMoment B raw7685step2 raw7685step2Labels = mixedMoment B raw7685step3 raw7685step3Labels := by
      have ha : raw7685step3 = -raw7685step2 := by apply Matrix.ext; change ∀ i j, raw7685step3 i j = -(raw7685step2 i j); unfold raw7685step3 raw7685step2; decide +kernel
      have hl : raw7685step3Labels = raw7685step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7685step3 raw7685step3Labels = mixedMoment B raw7685step4 raw7685step4Labels := by
      have ha : raw7685step4 = raw7685step3 := by apply Matrix.ext; unfold raw7685step4 raw7685step3; decide +kernel
      have hl : raw7685step3Labels = labelEmbedding1 ∘ raw7685step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7685step3 raw7685step3Labels raw7685step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw7686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7686Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7686step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7686step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7686 raw7686Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw7686 raw7686Labels = mixedMoment B raw7686step0 raw7686step0Labels := by
      have hz : ∀ j, raw7686 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7686step0 = (fun i j => raw7686 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7686step0 raw7686; decide +kernel
      have hl : raw7686step0Labels = raw7686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7686 raw7686Labels permutation265 hz
    mixedMoment B raw7686step0 raw7686step0Labels = mixedMoment B raw7686step1 raw7686step1Labels := by
      have ha : raw7686step1 = (fun i j => raw7686step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7686step1 raw7686step0; decide +kernel
      have hl : raw7686step1Labels = raw7686step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7686step0 raw7686step0Labels permutation32 permutation7
    mixedMoment B raw7686step1 raw7686step1Labels = mixedMoment B raw7686step2 raw7686step2Labels := by
      have ha : raw7686step2 = raw7686step1 := by apply Matrix.ext; unfold raw7686step2 raw7686step1; decide +kernel
      have hl : raw7686step1Labels = labelEmbedding1 ∘ raw7686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7686step1 raw7686step1Labels raw7686step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw7687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7687Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7687step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7687step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7687step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7687step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7687step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7687 raw7687Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw7687 raw7687Labels = mixedMoment B raw7687step0 raw7687step0Labels := by
      have hz : ∀ j, raw7687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7687step0 = (fun i j => raw7687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7687step0 raw7687; decide +kernel
      have hl : raw7687step0Labels = raw7687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7687 raw7687Labels permutation434 hz
    mixedMoment B raw7687step0 raw7687step0Labels = mixedMoment B raw7687step1 raw7687step1Labels := by
      have hz : ∀ j, raw7687step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7687step1 = (fun i j => raw7687step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7687step1 raw7687step0; decide +kernel
      have hl : raw7687step1Labels = raw7687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7687step0 raw7687step0Labels permutation56 hz
    mixedMoment B raw7687step1 raw7687step1Labels = mixedMoment B raw7687step2 raw7687step2Labels := by
      have ha : raw7687step2 = (fun i j => raw7687step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7687step2 raw7687step1; decide +kernel
      have hl : raw7687step2Labels = raw7687step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7687step1 raw7687step1Labels permutation8 permutation7
    mixedMoment B raw7687step2 raw7687step2Labels = mixedMoment B raw7687step3 raw7687step3Labels := by
      have ha : raw7687step3 = raw7687step2 := by apply Matrix.ext; unfold raw7687step3 raw7687step2; decide +kernel
      have hl : raw7687step2Labels = labelEmbedding1 ∘ raw7687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7687step2 raw7687step2Labels raw7687step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw7688 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7688Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7688step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7688step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7688step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-1, -1, 2]]
def raw7688step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7688step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -3, 0], ![-1, 2, -1], ![-2, 1, 1]]
def raw7688step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7688step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw7688step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7688step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw7688step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7688 raw7688Labels = mixedMoment B node3231 node3231Labels := by
  calc
    mixedMoment B raw7688 raw7688Labels = mixedMoment B raw7688step0 raw7688step0Labels := by
      have hz : ∀ j, raw7688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7688step0 = (fun i j => raw7688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7688step0 raw7688; decide +kernel
      have hl : raw7688step0Labels = raw7688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7688 raw7688Labels permutation434 hz
    mixedMoment B raw7688step0 raw7688step0Labels = mixedMoment B raw7688step1 raw7688step1Labels := by
      have hz : ∀ j, raw7688step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7688step1 = (fun i j => raw7688step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7688step1 raw7688step0; decide +kernel
      have hl : raw7688step1Labels = raw7688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7688step0 raw7688step0Labels permutation80 hz
    mixedMoment B raw7688step1 raw7688step1Labels = mixedMoment B raw7688step2 raw7688step2Labels := by
      have hz : ∀ j, raw7688step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7688step2 = (fun i j => raw7688step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7688step2 raw7688step1; decide +kernel
      have hl : raw7688step2Labels = raw7688step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7688step1 raw7688step1Labels permutation14 hz
    mixedMoment B raw7688step2 raw7688step2Labels = mixedMoment B raw7688step3 raw7688step3Labels := by
      have ha : raw7688step3 = (fun i j => raw7688step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7688step3 raw7688step2; decide +kernel
      have hl : raw7688step3Labels = raw7688step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7688step2 raw7688step2Labels permutation3 permutation5
    mixedMoment B raw7688step3 raw7688step3Labels = mixedMoment B raw7688step4 raw7688step4Labels := by
      have ha : raw7688step4 = -raw7688step3 := by apply Matrix.ext; change ∀ i j, raw7688step4 i j = -(raw7688step3 i j); unfold raw7688step4 raw7688step3; decide +kernel
      have hl : raw7688step4Labels = raw7688step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7688step4 raw7688step4Labels = mixedMoment B raw7688step5 raw7688step5Labels := by
      have ha : raw7688step5 = raw7688step4 := by apply Matrix.ext; unfold raw7688step5 raw7688step4; decide +kernel
      have hl : raw7688step4Labels = labelEmbedding1 ∘ raw7688step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7688step4 raw7688step4Labels raw7688step5Labels labelEmbedding1 hl
    _ = mixedMoment B node3231 node3231Labels := by rfl

def raw7689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7689Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7689step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7689step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7689step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7689step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7689step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7689 raw7689Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw7689 raw7689Labels = mixedMoment B raw7689step0 raw7689step0Labels := by
      have hz : ∀ j, raw7689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7689step0 = (fun i j => raw7689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7689step0 raw7689; decide +kernel
      have hl : raw7689step0Labels = raw7689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7689 raw7689Labels permutation434 hz
    mixedMoment B raw7689step0 raw7689step0Labels = mixedMoment B raw7689step1 raw7689step1Labels := by
      have hz : ∀ j, raw7689step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7689step1 = (fun i j => raw7689step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7689step1 raw7689step0; decide +kernel
      have hl : raw7689step1Labels = raw7689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7689step0 raw7689step0Labels permutation56 hz
    mixedMoment B raw7689step1 raw7689step1Labels = mixedMoment B raw7689step2 raw7689step2Labels := by
      have ha : raw7689step2 = (fun i j => raw7689step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7689step2 raw7689step1; decide +kernel
      have hl : raw7689step2Labels = raw7689step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7689step1 raw7689step1Labels permutation8 permutation7
    mixedMoment B raw7689step2 raw7689step2Labels = mixedMoment B raw7689step3 raw7689step3Labels := by
      have ha : raw7689step3 = raw7689step2 := by apply Matrix.ext; unfold raw7689step3 raw7689step2; decide +kernel
      have hl : raw7689step2Labels = labelEmbedding1 ∘ raw7689step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7689step2 raw7689step2Labels raw7689step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw7690 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7690Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7690step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7690step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7690step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7690step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7690 raw7690Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw7690 raw7690Labels = mixedMoment B raw7690step0 raw7690step0Labels := by
      have hz : ∀ j, raw7690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7690step0 = (fun i j => raw7690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7690step0 raw7690; decide +kernel
      have hl : raw7690step0Labels = raw7690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7690 raw7690Labels permutation346 hz
    mixedMoment B raw7690step0 raw7690step0Labels = mixedMoment B raw7690step1 raw7690step1Labels := by
      have hz : ∀ j, raw7690step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7690step1 = (fun i j => raw7690step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7690step1 raw7690step0; decide +kernel
      have hl : raw7690step1Labels = raw7690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7690step0 raw7690step0Labels permutation56 hz
    mixedMoment B raw7690step1 raw7690step1Labels = mixedMoment B raw7690step2 raw7690step2Labels := by
      have ha : raw7690step2 = (fun i j => raw7690step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7690step2 raw7690step1; decide +kernel
      have hl : raw7690step2Labels = raw7690step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7690step1 raw7690step1Labels permutation8 permutation7
    mixedMoment B raw7690step2 raw7690step2Labels = mixedMoment B raw7690step3 raw7690step3Labels := by
      have ha : raw7690step3 = raw7690step2 := by apply Matrix.ext; unfold raw7690step3 raw7690step2; decide +kernel
      have hl : raw7690step2Labels = labelEmbedding1 ∘ raw7690step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7690step2 raw7690step2Labels raw7690step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw7691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7691Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7691step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7691step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7691step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, -1, 2]]
def raw7691step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7691step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7691step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7691step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7691step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7691 raw7691Labels = mixedMoment B node3123 node3123Labels := by
  calc
    mixedMoment B raw7691 raw7691Labels = mixedMoment B raw7691step0 raw7691step0Labels := by
      have hz : ∀ j, raw7691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7691step0 = (fun i j => raw7691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7691step0 raw7691; decide +kernel
      have hl : raw7691step0Labels = raw7691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7691 raw7691Labels permutation434 hz
    mixedMoment B raw7691step0 raw7691step0Labels = mixedMoment B raw7691step1 raw7691step1Labels := by
      have hz : ∀ j, raw7691step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7691step1 = (fun i j => raw7691step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7691step1 raw7691step0; decide +kernel
      have hl : raw7691step1Labels = raw7691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7691step0 raw7691step0Labels permutation80 hz
    mixedMoment B raw7691step1 raw7691step1Labels = mixedMoment B raw7691step2 raw7691step2Labels := by
      have hz : ∀ j, raw7691step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7691step2 = (fun i j => raw7691step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7691step2 raw7691step1; decide +kernel
      have hl : raw7691step2Labels = raw7691step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7691step1 raw7691step1Labels permutation14 hz
    mixedMoment B raw7691step2 raw7691step2Labels = mixedMoment B raw7691step3 raw7691step3Labels := by
      have ha : raw7691step3 = (fun i j => raw7691step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7691step3 raw7691step2; decide +kernel
      have hl : raw7691step3Labels = raw7691step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7691step2 raw7691step2Labels permutation2 permutation7
    mixedMoment B raw7691step3 raw7691step3Labels = mixedMoment B raw7691step4 raw7691step4Labels := by
      have ha : raw7691step4 = raw7691step3 := by apply Matrix.ext; unfold raw7691step4 raw7691step3; decide +kernel
      have hl : raw7691step3Labels = labelEmbedding1 ∘ raw7691step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7691step3 raw7691step3Labels raw7691step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3123 node3123Labels := by rfl

def raw7692 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7692step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7692step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7692 raw7692Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw7692 raw7692Labels = mixedMoment B raw7692step0 raw7692step0Labels := by
      have hz : ∀ j, raw7692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7692step0 = (fun i j => raw7692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7692step0 raw7692; decide +kernel
      have hl : raw7692step0Labels = raw7692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7692 raw7692Labels permutation434 hz
    mixedMoment B raw7692step0 raw7692step0Labels = mixedMoment B raw7692step1 raw7692step1Labels := by
      have hz : ∀ j, raw7692step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7692step1 = (fun i j => raw7692step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7692step1 raw7692step0; decide +kernel
      have hl : raw7692step1Labels = raw7692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7692step0 raw7692step0Labels permutation56 hz
    mixedMoment B raw7692step1 raw7692step1Labels = mixedMoment B raw7692step2 raw7692step2Labels := by
      have ha : raw7692step2 = (fun i j => raw7692step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7692step2 raw7692step1; decide +kernel
      have hl : raw7692step2Labels = raw7692step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7692step1 raw7692step1Labels permutation10 permutation2
    mixedMoment B raw7692step2 raw7692step2Labels = mixedMoment B raw7692step3 raw7692step3Labels := by
      have ha : raw7692step3 = -raw7692step2 := by apply Matrix.ext; change ∀ i j, raw7692step3 i j = -(raw7692step2 i j); unfold raw7692step3 raw7692step2; decide +kernel
      have hl : raw7692step3Labels = raw7692step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw7693 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7693step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7693 raw7693Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw7693 raw7693Labels = mixedMoment B raw7693step0 raw7693step0Labels := by
      have hz : ∀ j, raw7693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7693step0 = (fun i j => raw7693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7693step0 raw7693; decide +kernel
      have hl : raw7693step0Labels = raw7693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7693 raw7693Labels permutation346 hz
    mixedMoment B raw7693step0 raw7693step0Labels = mixedMoment B raw7693step1 raw7693step1Labels := by
      have hz : ∀ j, raw7693step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7693step1 = (fun i j => raw7693step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7693step1 raw7693step0; decide +kernel
      have hl : raw7693step1Labels = raw7693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7693step0 raw7693step0Labels permutation56 hz
    mixedMoment B raw7693step1 raw7693step1Labels = mixedMoment B raw7693step2 raw7693step2Labels := by
      have ha : raw7693step2 = (fun i j => raw7693step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7693step2 raw7693step1; decide +kernel
      have hl : raw7693step2Labels = raw7693step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7693step1 raw7693step1Labels permutation10 permutation2
    mixedMoment B raw7693step2 raw7693step2Labels = mixedMoment B raw7693step3 raw7693step3Labels := by
      have ha : raw7693step3 = -raw7693step2 := by apply Matrix.ext; change ∀ i j, raw7693step3 i j = -(raw7693step2 i j); unfold raw7693step3 raw7693step2; decide +kernel
      have hl : raw7693step3Labels = raw7693step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw7694 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7694step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw7694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7694step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]
def raw7694step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7694 raw7694Labels = mixedMoment B node3629 node3629Labels := by
  calc
    mixedMoment B raw7694 raw7694Labels = mixedMoment B raw7694step0 raw7694step0Labels := by
      have hz : ∀ j, raw7694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7694step0 = (fun i j => raw7694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7694step0 raw7694; decide +kernel
      have hl : raw7694step0Labels = raw7694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7694 raw7694Labels permutation434 hz
    mixedMoment B raw7694step0 raw7694step0Labels = mixedMoment B raw7694step1 raw7694step1Labels := by
      have hz : ∀ j, raw7694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7694step1 = (fun i j => raw7694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7694step1 raw7694step0; decide +kernel
      have hl : raw7694step1Labels = raw7694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7694step0 raw7694step0Labels permutation80 hz
    mixedMoment B raw7694step1 raw7694step1Labels = mixedMoment B raw7694step2 raw7694step2Labels := by
      have hz : ∀ j, raw7694step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7694step2 = (fun i j => raw7694step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7694step2 raw7694step1; decide +kernel
      have hl : raw7694step2Labels = raw7694step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7694step1 raw7694step1Labels permutation14 hz
    mixedMoment B raw7694step2 raw7694step2Labels = mixedMoment B raw7694step3 raw7694step3Labels := by
      have ha : raw7694step3 = -raw7694step2 := by apply Matrix.ext; change ∀ i j, raw7694step3 i j = -(raw7694step2 i j); unfold raw7694step3 raw7694step2; decide +kernel
      have hl : raw7694step3Labels = raw7694step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3629 node3629Labels := by rfl

def raw7695 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7695step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-3, 1, 2]]
def raw7695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7695step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7695step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7695 raw7695Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw7695 raw7695Labels = mixedMoment B raw7695step0 raw7695step0Labels := by
      have hz : ∀ j, raw7695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7695step0 = (fun i j => raw7695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7695step0 raw7695; decide +kernel
      have hl : raw7695step0Labels = raw7695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7695 raw7695Labels permutation434 hz
    mixedMoment B raw7695step0 raw7695step0Labels = mixedMoment B raw7695step1 raw7695step1Labels := by
      have hz : ∀ j, raw7695step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7695step1 = (fun i j => raw7695step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7695step1 raw7695step0; decide +kernel
      have hl : raw7695step1Labels = raw7695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7695step0 raw7695step0Labels permutation80 hz
    mixedMoment B raw7695step1 raw7695step1Labels = mixedMoment B raw7695step2 raw7695step2Labels := by
      have hz : ∀ j, raw7695step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7695step2 = (fun i j => raw7695step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7695step2 raw7695step1; decide +kernel
      have hl : raw7695step2Labels = raw7695step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7695step1 raw7695step1Labels permutation14 hz
    mixedMoment B raw7695step2 raw7695step2Labels = mixedMoment B raw7695step3 raw7695step3Labels := by
      have ha : raw7695step3 = (fun i j => raw7695step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7695step3 raw7695step2; decide +kernel
      have hl : raw7695step3Labels = raw7695step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7695step2 raw7695step2Labels permutation7 permutation2
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw7696 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw7696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7696step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7696step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7696 raw7696Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw7696 raw7696Labels = mixedMoment B raw7696step0 raw7696step0Labels := by
      have hz : ∀ j, raw7696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7696step0 = (fun i j => raw7696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7696step0 raw7696; decide +kernel
      have hl : raw7696step0Labels = raw7696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7696 raw7696Labels permutation434 hz
    mixedMoment B raw7696step0 raw7696step0Labels = mixedMoment B raw7696step1 raw7696step1Labels := by
      have hz : ∀ j, raw7696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7696step1 = (fun i j => raw7696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7696step1 raw7696step0; decide +kernel
      have hl : raw7696step1Labels = raw7696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7696step0 raw7696step0Labels permutation80 hz
    mixedMoment B raw7696step1 raw7696step1Labels = mixedMoment B raw7696step2 raw7696step2Labels := by
      have ha : raw7696step2 = (fun i j => raw7696step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7696step2 raw7696step1; decide +kernel
      have hl : raw7696step2Labels = raw7696step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7696step1 raw7696step1Labels permutation12 permutation4
    mixedMoment B raw7696step2 raw7696step2Labels = mixedMoment B raw7696step3 raw7696step3Labels := by
      have ha : raw7696step3 = -raw7696step2 := by apply Matrix.ext; change ∀ i j, raw7696step3 i j = -(raw7696step2 i j); unfold raw7696step3 raw7696step2; decide +kernel
      have hl : raw7696step3Labels = raw7696step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3632 node3632Labels := by rfl

def raw7697 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7697step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, -1, 2]]
def raw7697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7697step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, -1, 2]]
def raw7697step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7697step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]
def raw7697step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7697 raw7697Labels = mixedMoment B node3635 node3635Labels := by
  calc
    mixedMoment B raw7697 raw7697Labels = mixedMoment B raw7697step0 raw7697step0Labels := by
      have hz : ∀ j, raw7697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7697step0 = (fun i j => raw7697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7697step0 raw7697; decide +kernel
      have hl : raw7697step0Labels = raw7697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7697 raw7697Labels permutation434 hz
    mixedMoment B raw7697step0 raw7697step0Labels = mixedMoment B raw7697step1 raw7697step1Labels := by
      have hz : ∀ j, raw7697step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7697step1 = (fun i j => raw7697step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7697step1 raw7697step0; decide +kernel
      have hl : raw7697step1Labels = raw7697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7697step0 raw7697step0Labels permutation80 hz
    mixedMoment B raw7697step1 raw7697step1Labels = mixedMoment B raw7697step2 raw7697step2Labels := by
      have hz : ∀ j, raw7697step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7697step2 = (fun i j => raw7697step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7697step2 raw7697step1; decide +kernel
      have hl : raw7697step2Labels = raw7697step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7697step1 raw7697step1Labels permutation14 hz
    mixedMoment B raw7697step2 raw7697step2Labels = mixedMoment B raw7697step3 raw7697step3Labels := by
      have ha : raw7697step3 = (fun i j => raw7697step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7697step3 raw7697step2; decide +kernel
      have hl : raw7697step3Labels = raw7697step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7697step2 raw7697step2Labels permutation2 permutation4
    mixedMoment B raw7697step3 raw7697step3Labels = mixedMoment B raw7697step4 raw7697step4Labels := by
      have ha : raw7697step4 = -raw7697step3 := by apply Matrix.ext; change ∀ i j, raw7697step4 i j = -(raw7697step3 i j); unfold raw7697step4 raw7697step3; decide +kernel
      have hl : raw7697step4Labels = raw7697step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3635 node3635Labels := by rfl

def raw7698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7698step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-1, -1, 2]]
def raw7698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7698step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw7698step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7698step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw7698step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7698 raw7698Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw7698 raw7698Labels = mixedMoment B raw7698step0 raw7698step0Labels := by
      have hz : ∀ j, raw7698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7698step0 = (fun i j => raw7698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7698step0 raw7698; decide +kernel
      have hl : raw7698step0Labels = raw7698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7698 raw7698Labels permutation434 hz
    mixedMoment B raw7698step0 raw7698step0Labels = mixedMoment B raw7698step1 raw7698step1Labels := by
      have hz : ∀ j, raw7698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7698step1 = (fun i j => raw7698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7698step1 raw7698step0; decide +kernel
      have hl : raw7698step1Labels = raw7698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7698step0 raw7698step0Labels permutation80 hz
    mixedMoment B raw7698step1 raw7698step1Labels = mixedMoment B raw7698step2 raw7698step2Labels := by
      have hz : ∀ j, raw7698step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7698step2 = (fun i j => raw7698step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7698step2 raw7698step1; decide +kernel
      have hl : raw7698step2Labels = raw7698step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7698step1 raw7698step1Labels permutation14 hz
    mixedMoment B raw7698step2 raw7698step2Labels = mixedMoment B raw7698step3 raw7698step3Labels := by
      have ha : raw7698step3 = (fun i j => raw7698step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7698step3 raw7698step2; decide +kernel
      have hl : raw7698step3Labels = raw7698step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7698step2 raw7698step2Labels permutation3 permutation4
    mixedMoment B raw7698step3 raw7698step3Labels = mixedMoment B raw7698step4 raw7698step4Labels := by
      have ha : raw7698step4 = -raw7698step3 := by apply Matrix.ext; change ∀ i j, raw7698step4 i j = -(raw7698step3 i j); unfold raw7698step4 raw7698step3; decide +kernel
      have hl : raw7698step4Labels = raw7698step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2293 node2293Labels := by rfl

def raw7699 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw7699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7699step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7699 raw7699Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw7699 raw7699Labels = mixedMoment B raw7699step0 raw7699step0Labels := by
      have hz : ∀ j, raw7699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7699step0 = (fun i j => raw7699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7699step0 raw7699; decide +kernel
      have hl : raw7699step0Labels = raw7699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7699 raw7699Labels permutation434 hz
    mixedMoment B raw7699step0 raw7699step0Labels = mixedMoment B raw7699step1 raw7699step1Labels := by
      have hz : ∀ j, raw7699step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7699step1 = (fun i j => raw7699step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7699step1 raw7699step0; decide +kernel
      have hl : raw7699step1Labels = raw7699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7699step0 raw7699step0Labels permutation56 hz
    mixedMoment B raw7699step1 raw7699step1Labels = mixedMoment B raw7699step2 raw7699step2Labels := by
      have ha : raw7699step2 = (fun i j => raw7699step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7699step2 raw7699step1; decide +kernel
      have hl : raw7699step2Labels = raw7699step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7699step1 raw7699step1Labels permutation9 permutation4
    mixedMoment B raw7699step2 raw7699step2Labels = mixedMoment B raw7699step3 raw7699step3Labels := by
      have ha : raw7699step3 = -raw7699step2 := by apply Matrix.ext; change ∀ i j, raw7699step3 i j = -(raw7699step2 i j); unfold raw7699step3 raw7699step2; decide +kernel
      have hl : raw7699step3Labels = raw7699step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw7700 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw7700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7700step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7700 raw7700Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw7700 raw7700Labels = mixedMoment B raw7700step0 raw7700step0Labels := by
      have hz : ∀ j, raw7700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7700step0 = (fun i j => raw7700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7700step0 raw7700; decide +kernel
      have hl : raw7700step0Labels = raw7700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7700 raw7700Labels permutation346 hz
    mixedMoment B raw7700step0 raw7700step0Labels = mixedMoment B raw7700step1 raw7700step1Labels := by
      have hz : ∀ j, raw7700step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7700step1 = (fun i j => raw7700step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7700step1 raw7700step0; decide +kernel
      have hl : raw7700step1Labels = raw7700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7700step0 raw7700step0Labels permutation56 hz
    mixedMoment B raw7700step1 raw7700step1Labels = mixedMoment B raw7700step2 raw7700step2Labels := by
      have ha : raw7700step2 = (fun i j => raw7700step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7700step2 raw7700step1; decide +kernel
      have hl : raw7700step2Labels = raw7700step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7700step1 raw7700step1Labels permutation9 permutation4
    mixedMoment B raw7700step2 raw7700step2Labels = mixedMoment B raw7700step3 raw7700step3Labels := by
      have ha : raw7700step3 = -raw7700step2 := by apply Matrix.ext; change ∀ i j, raw7700step3 i j = -(raw7700step2 i j); unfold raw7700step3 raw7700step2; decide +kernel
      have hl : raw7700step3Labels = raw7700step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw7701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7701step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7701step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7701step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7701 raw7701Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw7701 raw7701Labels = mixedMoment B raw7701step0 raw7701step0Labels := by
      have hz : ∀ j, raw7701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7701step0 = (fun i j => raw7701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7701step0 raw7701; decide +kernel
      have hl : raw7701step0Labels = raw7701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7701 raw7701Labels permutation434 hz
    mixedMoment B raw7701step0 raw7701step0Labels = mixedMoment B raw7701step1 raw7701step1Labels := by
      have hz : ∀ j, raw7701step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7701step1 = (fun i j => raw7701step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7701step1 raw7701step0; decide +kernel
      have hl : raw7701step1Labels = raw7701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7701step0 raw7701step0Labels permutation80 hz
    mixedMoment B raw7701step1 raw7701step1Labels = mixedMoment B raw7701step2 raw7701step2Labels := by
      have ha : raw7701step2 = (fun i j => raw7701step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7701step2 raw7701step1; decide +kernel
      have hl : raw7701step2Labels = raw7701step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7701step1 raw7701step1Labels permutation23 permutation6
    mixedMoment B raw7701step2 raw7701step2Labels = mixedMoment B raw7701step3 raw7701step3Labels := by
      have ha : raw7701step3 = raw7701step2 := by apply Matrix.ext; unfold raw7701step3 raw7701step2; decide +kernel
      have hl : raw7701step2Labels = labelEmbedding9 ∘ raw7701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7701step2 raw7701step2Labels raw7701step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw7702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7702step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7702step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7702step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7702 raw7702Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw7702 raw7702Labels = mixedMoment B raw7702step0 raw7702step0Labels := by
      have hz : ∀ j, raw7702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7702step0 = (fun i j => raw7702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7702step0 raw7702; decide +kernel
      have hl : raw7702step0Labels = raw7702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7702 raw7702Labels permutation434 hz
    mixedMoment B raw7702step0 raw7702step0Labels = mixedMoment B raw7702step1 raw7702step1Labels := by
      have hz : ∀ j, raw7702step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7702step1 = (fun i j => raw7702step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7702step1 raw7702step0; decide +kernel
      have hl : raw7702step1Labels = raw7702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7702step0 raw7702step0Labels permutation56 hz
    mixedMoment B raw7702step1 raw7702step1Labels = mixedMoment B raw7702step2 raw7702step2Labels := by
      have ha : raw7702step2 = (fun i j => raw7702step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7702step2 raw7702step1; decide +kernel
      have hl : raw7702step2Labels = raw7702step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7702step1 raw7702step1Labels permutation23 permutation6
    mixedMoment B raw7702step2 raw7702step2Labels = mixedMoment B raw7702step3 raw7702step3Labels := by
      have ha : raw7702step3 = raw7702step2 := by apply Matrix.ext; unfold raw7702step3 raw7702step2; decide +kernel
      have hl : raw7702step2Labels = labelEmbedding9 ∘ raw7702step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7702step2 raw7702step2Labels raw7702step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw7703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7703step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7703step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7703step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7703 raw7703Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw7703 raw7703Labels = mixedMoment B raw7703step0 raw7703step0Labels := by
      have hz : ∀ j, raw7703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7703step0 = (fun i j => raw7703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7703step0 raw7703; decide +kernel
      have hl : raw7703step0Labels = raw7703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7703 raw7703Labels permutation346 hz
    mixedMoment B raw7703step0 raw7703step0Labels = mixedMoment B raw7703step1 raw7703step1Labels := by
      have hz : ∀ j, raw7703step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7703step1 = (fun i j => raw7703step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7703step1 raw7703step0; decide +kernel
      have hl : raw7703step1Labels = raw7703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7703step0 raw7703step0Labels permutation56 hz
    mixedMoment B raw7703step1 raw7703step1Labels = mixedMoment B raw7703step2 raw7703step2Labels := by
      have ha : raw7703step2 = (fun i j => raw7703step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7703step2 raw7703step1; decide +kernel
      have hl : raw7703step2Labels = raw7703step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7703step1 raw7703step1Labels permutation23 permutation6
    mixedMoment B raw7703step2 raw7703step2Labels = mixedMoment B raw7703step3 raw7703step3Labels := by
      have ha : raw7703step3 = raw7703step2 := by apply Matrix.ext; unfold raw7703step3 raw7703step2; decide +kernel
      have hl : raw7703step2Labels = labelEmbedding9 ∘ raw7703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7703step2 raw7703step2Labels raw7703step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw7704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7704step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]
def raw7704step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7704step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw7704step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7704step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw7704step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7704step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw7704step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7704 raw7704Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw7704 raw7704Labels = mixedMoment B raw7704step0 raw7704step0Labels := by
      have hz : ∀ j, raw7704 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7704step0 = (fun i j => raw7704 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7704step0 raw7704; decide +kernel
      have hl : raw7704step0Labels = raw7704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7704 raw7704Labels permutation434 hz
    mixedMoment B raw7704step0 raw7704step0Labels = mixedMoment B raw7704step1 raw7704step1Labels := by
      have hz : ∀ j, raw7704step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7704step1 = (fun i j => raw7704step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7704step1 raw7704step0; decide +kernel
      have hl : raw7704step1Labels = raw7704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7704step0 raw7704step0Labels permutation80 hz
    mixedMoment B raw7704step1 raw7704step1Labels = mixedMoment B raw7704step2 raw7704step2Labels := by
      have hz : ∀ j, raw7704step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7704step2 = (fun i j => raw7704step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7704step2 raw7704step1; decide +kernel
      have hl : raw7704step2Labels = raw7704step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7704step1 raw7704step1Labels permutation14 hz
    mixedMoment B raw7704step2 raw7704step2Labels = mixedMoment B raw7704step3 raw7704step3Labels := by
      have ha : raw7704step3 = (fun i j => raw7704step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7704step3 raw7704step2; decide +kernel
      have hl : raw7704step3Labels = raw7704step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7704step2 raw7704step2Labels permutation4 permutation4
    mixedMoment B raw7704step3 raw7704step3Labels = mixedMoment B raw7704step4 raw7704step4Labels := by
      have ha : raw7704step4 = -raw7704step3 := by apply Matrix.ext; change ∀ i j, raw7704step4 i j = -(raw7704step3 i j); unfold raw7704step4 raw7704step3; decide +kernel
      have hl : raw7704step4Labels = raw7704step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7704step4 raw7704step4Labels = mixedMoment B raw7704step5 raw7704step5Labels := by
      have ha : raw7704step5 = raw7704step4 := by apply Matrix.ext; unfold raw7704step5 raw7704step4; decide +kernel
      have hl : raw7704step4Labels = labelEmbedding7 ∘ raw7704step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7704step4 raw7704step4Labels raw7704step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw7705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7705step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![1, -2, 1]]
def raw7705step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7705step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw7705step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7705step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw7705step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7705 raw7705Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw7705 raw7705Labels = mixedMoment B raw7705step0 raw7705step0Labels := by
      have hz : ∀ j, raw7705 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7705step0 = (fun i j => raw7705 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7705step0 raw7705; decide +kernel
      have hl : raw7705step0Labels = raw7705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7705 raw7705Labels permutation434 hz
    mixedMoment B raw7705step0 raw7705step0Labels = mixedMoment B raw7705step1 raw7705step1Labels := by
      have hz : ∀ j, raw7705step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7705step1 = (fun i j => raw7705step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7705step1 raw7705step0; decide +kernel
      have hl : raw7705step1Labels = raw7705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7705step0 raw7705step0Labels permutation80 hz
    mixedMoment B raw7705step1 raw7705step1Labels = mixedMoment B raw7705step2 raw7705step2Labels := by
      have hz : ∀ j, raw7705step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7705step2 = (fun i j => raw7705step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7705step2 raw7705step1; decide +kernel
      have hl : raw7705step2Labels = raw7705step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7705step1 raw7705step1Labels permutation14 hz
    mixedMoment B raw7705step2 raw7705step2Labels = mixedMoment B raw7705step3 raw7705step3Labels := by
      have ha : raw7705step3 = (fun i j => raw7705step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7705step3 raw7705step2; decide +kernel
      have hl : raw7705step3Labels = raw7705step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7705step2 raw7705step2Labels permutation5 permutation6
    mixedMoment B raw7705step3 raw7705step3Labels = mixedMoment B raw7705step4 raw7705step4Labels := by
      have ha : raw7705step4 = raw7705step3 := by apply Matrix.ext; unfold raw7705step4 raw7705step3; decide +kernel
      have hl : raw7705step3Labels = labelEmbedding9 ∘ raw7705step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7705step3 raw7705step3Labels raw7705step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw7706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7706step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw7706step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw7706step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7706 raw7706Labels = mixedMoment B node4614 node4614Labels := by
  calc
    mixedMoment B raw7706 raw7706Labels = mixedMoment B raw7706step0 raw7706step0Labels := by
      have hz : ∀ j, raw7706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7706step0 = (fun i j => raw7706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7706step0 raw7706; decide +kernel
      have hl : raw7706step0Labels = raw7706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7706 raw7706Labels permutation434 hz
    mixedMoment B raw7706step0 raw7706step0Labels = mixedMoment B raw7706step1 raw7706step1Labels := by
      have hz : ∀ j, raw7706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7706step1 = (fun i j => raw7706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7706step1 raw7706step0; decide +kernel
      have hl : raw7706step1Labels = raw7706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7706step0 raw7706step0Labels permutation80 hz
    mixedMoment B raw7706step1 raw7706step1Labels = mixedMoment B raw7706step2 raw7706step2Labels := by
      have ha : raw7706step2 = (fun i j => raw7706step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7706step2 raw7706step1; decide +kernel
      have hl : raw7706step2Labels = raw7706step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7706step1 raw7706step1Labels permutation10 permutation3
    mixedMoment B raw7706step2 raw7706step2Labels = mixedMoment B raw7706step3 raw7706step3Labels := by
      have ha : raw7706step3 = raw7706step2 := by apply Matrix.ext; unfold raw7706step3 raw7706step2; decide +kernel
      have hl : raw7706step2Labels = labelEmbedding6 ∘ raw7706step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7706step2 raw7706step2Labels raw7706step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4614 node4614Labels := by rfl

def raw7707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7707step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7707 raw7707Labels = mixedMoment B node5106 node5106Labels := by
  calc
    mixedMoment B raw7707 raw7707Labels = mixedMoment B raw7707step0 raw7707step0Labels := by
      have hz : ∀ j, raw7707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7707step0 = (fun i j => raw7707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7707step0 raw7707; decide +kernel
      have hl : raw7707step0Labels = raw7707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7707 raw7707Labels permutation434 hz
    mixedMoment B raw7707step0 raw7707step0Labels = mixedMoment B raw7707step1 raw7707step1Labels := by
      have ha : raw7707step1 = (fun i j => raw7707step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7707step1 raw7707step0; decide +kernel
      have hl : raw7707step1Labels = raw7707step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7707step0 raw7707step0Labels permutation136 permutation5
    mixedMoment B raw7707step1 raw7707step1Labels = mixedMoment B raw7707step2 raw7707step2Labels := by
      have ha : raw7707step2 = raw7707step1 := by apply Matrix.ext; unfold raw7707step2 raw7707step1; decide +kernel
      have hl : raw7707step1Labels = labelEmbedding8 ∘ raw7707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7707step1 raw7707step1Labels raw7707step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5106 node5106Labels := by rfl

def raw7708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7708step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7708step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7708 raw7708Labels = mixedMoment B node5106 node5106Labels := by
  calc
    mixedMoment B raw7708 raw7708Labels = mixedMoment B raw7708step0 raw7708step0Labels := by
      have hz : ∀ j, raw7708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7708step0 = (fun i j => raw7708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7708step0 raw7708; decide +kernel
      have hl : raw7708step0Labels = raw7708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7708 raw7708Labels permutation346 hz
    mixedMoment B raw7708step0 raw7708step0Labels = mixedMoment B raw7708step1 raw7708step1Labels := by
      have ha : raw7708step1 = (fun i j => raw7708step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7708step1 raw7708step0; decide +kernel
      have hl : raw7708step1Labels = raw7708step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7708step0 raw7708step0Labels permutation136 permutation5
    mixedMoment B raw7708step1 raw7708step1Labels = mixedMoment B raw7708step2 raw7708step2Labels := by
      have ha : raw7708step2 = raw7708step1 := by apply Matrix.ext; unfold raw7708step2 raw7708step1; decide +kernel
      have hl : raw7708step1Labels = labelEmbedding8 ∘ raw7708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7708step1 raw7708step1Labels raw7708step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5106 node5106Labels := by rfl

def raw7709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw7709step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw7709step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7709step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw7709step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7709 raw7709Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw7709 raw7709Labels = mixedMoment B raw7709step0 raw7709step0Labels := by
      have hz : ∀ j, raw7709 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7709step0 = (fun i j => raw7709 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7709step0 raw7709; decide +kernel
      have hl : raw7709step0Labels = raw7709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7709 raw7709Labels permutation434 hz
    mixedMoment B raw7709step0 raw7709step0Labels = mixedMoment B raw7709step1 raw7709step1Labels := by
      have hz : ∀ j, raw7709step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7709step1 = (fun i j => raw7709step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7709step1 raw7709step0; decide +kernel
      have hl : raw7709step1Labels = raw7709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7709step0 raw7709step0Labels permutation80 hz
    mixedMoment B raw7709step1 raw7709step1Labels = mixedMoment B raw7709step2 raw7709step2Labels := by
      have ha : raw7709step2 = (fun i j => raw7709step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7709step2 raw7709step1; decide +kernel
      have hl : raw7709step2Labels = raw7709step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7709step1 raw7709step1Labels permutation20 permutation4
    mixedMoment B raw7709step2 raw7709step2Labels = mixedMoment B raw7709step3 raw7709step3Labels := by
      have ha : raw7709step3 = -raw7709step2 := by apply Matrix.ext; change ∀ i j, raw7709step3 i j = -(raw7709step2 i j); unfold raw7709step3 raw7709step2; decide +kernel
      have hl : raw7709step3Labels = raw7709step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7709step3 raw7709step3Labels = mixedMoment B raw7709step4 raw7709step4Labels := by
      have ha : raw7709step4 = raw7709step3 := by apply Matrix.ext; unfold raw7709step4 raw7709step3; decide +kernel
      have hl : raw7709step3Labels = labelEmbedding7 ∘ raw7709step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7709step3 raw7709step3Labels raw7709step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw7710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7710step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7710step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7710step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7710 raw7710Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw7710 raw7710Labels = mixedMoment B raw7710step0 raw7710step0Labels := by
      have hz : ∀ j, raw7710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7710step0 = (fun i j => raw7710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7710step0 raw7710; decide +kernel
      have hl : raw7710step0Labels = raw7710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7710 raw7710Labels permutation434 hz
    mixedMoment B raw7710step0 raw7710step0Labels = mixedMoment B raw7710step1 raw7710step1Labels := by
      have hz : ∀ j, raw7710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7710step1 = (fun i j => raw7710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7710step1 raw7710step0; decide +kernel
      have hl : raw7710step1Labels = raw7710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7710step0 raw7710step0Labels permutation80 hz
    mixedMoment B raw7710step1 raw7710step1Labels = mixedMoment B raw7710step2 raw7710step2Labels := by
      have ha : raw7710step2 = (fun i j => raw7710step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7710step2 raw7710step1; decide +kernel
      have hl : raw7710step2Labels = raw7710step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7710step1 raw7710step1Labels permutation23 permutation6
    mixedMoment B raw7710step2 raw7710step2Labels = mixedMoment B raw7710step3 raw7710step3Labels := by
      have ha : raw7710step3 = raw7710step2 := by apply Matrix.ext; unfold raw7710step3 raw7710step2; decide +kernel
      have hl : raw7710step2Labels = labelEmbedding9 ∘ raw7710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7710step2 raw7710step2Labels raw7710step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw7711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw7711step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw7711step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7711 raw7711Labels = mixedMoment B node4614 node4614Labels := by
  calc
    mixedMoment B raw7711 raw7711Labels = mixedMoment B raw7711step0 raw7711step0Labels := by
      have hz : ∀ j, raw7711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7711step0 = (fun i j => raw7711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7711step0 raw7711; decide +kernel
      have hl : raw7711step0Labels = raw7711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7711 raw7711Labels permutation434 hz
    mixedMoment B raw7711step0 raw7711step0Labels = mixedMoment B raw7711step1 raw7711step1Labels := by
      have hz : ∀ j, raw7711step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7711step1 = (fun i j => raw7711step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7711step1 raw7711step0; decide +kernel
      have hl : raw7711step1Labels = raw7711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7711step0 raw7711step0Labels permutation56 hz
    mixedMoment B raw7711step1 raw7711step1Labels = mixedMoment B raw7711step2 raw7711step2Labels := by
      have ha : raw7711step2 = (fun i j => raw7711step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7711step2 raw7711step1; decide +kernel
      have hl : raw7711step2Labels = raw7711step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7711step1 raw7711step1Labels permutation10 permutation3
    mixedMoment B raw7711step2 raw7711step2Labels = mixedMoment B raw7711step3 raw7711step3Labels := by
      have ha : raw7711step3 = raw7711step2 := by apply Matrix.ext; unfold raw7711step3 raw7711step2; decide +kernel
      have hl : raw7711step2Labels = labelEmbedding6 ∘ raw7711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7711step2 raw7711step2Labels raw7711step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4614 node4614Labels := by rfl

def raw7712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7712step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7712step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7712 raw7712Labels = mixedMoment B node5106 node5106Labels := by
  calc
    mixedMoment B raw7712 raw7712Labels = mixedMoment B raw7712step0 raw7712step0Labels := by
      have hz : ∀ j, raw7712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7712step0 = (fun i j => raw7712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7712step0 raw7712; decide +kernel
      have hl : raw7712step0Labels = raw7712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7712 raw7712Labels permutation434 hz
    mixedMoment B raw7712step0 raw7712step0Labels = mixedMoment B raw7712step1 raw7712step1Labels := by
      have ha : raw7712step1 = (fun i j => raw7712step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7712step1 raw7712step0; decide +kernel
      have hl : raw7712step1Labels = raw7712step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7712step0 raw7712step0Labels permutation142 permutation5
    mixedMoment B raw7712step1 raw7712step1Labels = mixedMoment B raw7712step2 raw7712step2Labels := by
      have ha : raw7712step2 = raw7712step1 := by apply Matrix.ext; unfold raw7712step2 raw7712step1; decide +kernel
      have hl : raw7712step1Labels = labelEmbedding8 ∘ raw7712step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7712step1 raw7712step1Labels raw7712step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5106 node5106Labels := by rfl

def raw7713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7713step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7713step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7713 raw7713Labels = mixedMoment B node5106 node5106Labels := by
  calc
    mixedMoment B raw7713 raw7713Labels = mixedMoment B raw7713step0 raw7713step0Labels := by
      have hz : ∀ j, raw7713 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7713step0 = (fun i j => raw7713 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7713step0 raw7713; decide +kernel
      have hl : raw7713step0Labels = raw7713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7713 raw7713Labels permutation265 hz
    mixedMoment B raw7713step0 raw7713step0Labels = mixedMoment B raw7713step1 raw7713step1Labels := by
      have ha : raw7713step1 = (fun i j => raw7713step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7713step1 raw7713step0; decide +kernel
      have hl : raw7713step1Labels = raw7713step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7713step0 raw7713step0Labels permutation136 permutation5
    mixedMoment B raw7713step1 raw7713step1Labels = mixedMoment B raw7713step2 raw7713step2Labels := by
      have ha : raw7713step2 = raw7713step1 := by apply Matrix.ext; unfold raw7713step2 raw7713step1; decide +kernel
      have hl : raw7713step1Labels = labelEmbedding8 ∘ raw7713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7713step1 raw7713step1Labels raw7713step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5106 node5106Labels := by rfl

def raw7714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw7714step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7714step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw7714step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7714step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw7714step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7714 raw7714Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw7714 raw7714Labels = mixedMoment B raw7714step0 raw7714step0Labels := by
      have hz : ∀ j, raw7714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7714step0 = (fun i j => raw7714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7714step0 raw7714; decide +kernel
      have hl : raw7714step0Labels = raw7714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7714 raw7714Labels permutation434 hz
    mixedMoment B raw7714step0 raw7714step0Labels = mixedMoment B raw7714step1 raw7714step1Labels := by
      have hz : ∀ j, raw7714step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7714step1 = (fun i j => raw7714step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7714step1 raw7714step0; decide +kernel
      have hl : raw7714step1Labels = raw7714step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7714step0 raw7714step0Labels permutation56 hz
    mixedMoment B raw7714step1 raw7714step1Labels = mixedMoment B raw7714step2 raw7714step2Labels := by
      have ha : raw7714step2 = (fun i j => raw7714step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7714step2 raw7714step1; decide +kernel
      have hl : raw7714step2Labels = raw7714step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7714step1 raw7714step1Labels permutation20 permutation4
    mixedMoment B raw7714step2 raw7714step2Labels = mixedMoment B raw7714step3 raw7714step3Labels := by
      have ha : raw7714step3 = -raw7714step2 := by apply Matrix.ext; change ∀ i j, raw7714step3 i j = -(raw7714step2 i j); unfold raw7714step3 raw7714step2; decide +kernel
      have hl : raw7714step3Labels = raw7714step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7714step3 raw7714step3Labels = mixedMoment B raw7714step4 raw7714step4Labels := by
      have ha : raw7714step4 = raw7714step3 := by apply Matrix.ext; unfold raw7714step4 raw7714step3; decide +kernel
      have hl : raw7714step3Labels = labelEmbedding7 ∘ raw7714step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7714step3 raw7714step3Labels raw7714step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw7715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7715step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7715step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7715step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7715 raw7715Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw7715 raw7715Labels = mixedMoment B raw7715step0 raw7715step0Labels := by
      have hz : ∀ j, raw7715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7715step0 = (fun i j => raw7715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7715step0 raw7715; decide +kernel
      have hl : raw7715step0Labels = raw7715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7715 raw7715Labels permutation434 hz
    mixedMoment B raw7715step0 raw7715step0Labels = mixedMoment B raw7715step1 raw7715step1Labels := by
      have hz : ∀ j, raw7715step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7715step1 = (fun i j => raw7715step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7715step1 raw7715step0; decide +kernel
      have hl : raw7715step1Labels = raw7715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7715step0 raw7715step0Labels permutation56 hz
    mixedMoment B raw7715step1 raw7715step1Labels = mixedMoment B raw7715step2 raw7715step2Labels := by
      have ha : raw7715step2 = (fun i j => raw7715step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7715step2 raw7715step1; decide +kernel
      have hl : raw7715step2Labels = raw7715step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7715step1 raw7715step1Labels permutation23 permutation6
    mixedMoment B raw7715step2 raw7715step2Labels = mixedMoment B raw7715step3 raw7715step3Labels := by
      have ha : raw7715step3 = raw7715step2 := by apply Matrix.ext; unfold raw7715step3 raw7715step2; decide +kernel
      have hl : raw7715step2Labels = labelEmbedding9 ∘ raw7715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7715step2 raw7715step2Labels raw7715step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw7716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw7716step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7716step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw7716step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7716 raw7716Labels = mixedMoment B node4614 node4614Labels := by
  calc
    mixedMoment B raw7716 raw7716Labels = mixedMoment B raw7716step0 raw7716step0Labels := by
      have hz : ∀ j, raw7716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7716step0 = (fun i j => raw7716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7716step0 raw7716; decide +kernel
      have hl : raw7716step0Labels = raw7716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7716 raw7716Labels permutation346 hz
    mixedMoment B raw7716step0 raw7716step0Labels = mixedMoment B raw7716step1 raw7716step1Labels := by
      have hz : ∀ j, raw7716step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7716step1 = (fun i j => raw7716step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7716step1 raw7716step0; decide +kernel
      have hl : raw7716step1Labels = raw7716step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7716step0 raw7716step0Labels permutation56 hz
    mixedMoment B raw7716step1 raw7716step1Labels = mixedMoment B raw7716step2 raw7716step2Labels := by
      have ha : raw7716step2 = (fun i j => raw7716step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7716step2 raw7716step1; decide +kernel
      have hl : raw7716step2Labels = raw7716step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7716step1 raw7716step1Labels permutation10 permutation3
    mixedMoment B raw7716step2 raw7716step2Labels = mixedMoment B raw7716step3 raw7716step3Labels := by
      have ha : raw7716step3 = raw7716step2 := by apply Matrix.ext; unfold raw7716step3 raw7716step2; decide +kernel
      have hl : raw7716step2Labels = labelEmbedding6 ∘ raw7716step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7716step2 raw7716step2Labels raw7716step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4614 node4614Labels := by rfl

def raw7717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7717step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7717step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7717 raw7717Labels = mixedMoment B node5106 node5106Labels := by
  calc
    mixedMoment B raw7717 raw7717Labels = mixedMoment B raw7717step0 raw7717step0Labels := by
      have hz : ∀ j, raw7717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7717step0 = (fun i j => raw7717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7717step0 raw7717; decide +kernel
      have hl : raw7717step0Labels = raw7717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7717 raw7717Labels permutation346 hz
    mixedMoment B raw7717step0 raw7717step0Labels = mixedMoment B raw7717step1 raw7717step1Labels := by
      have ha : raw7717step1 = (fun i j => raw7717step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7717step1 raw7717step0; decide +kernel
      have hl : raw7717step1Labels = raw7717step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7717step0 raw7717step0Labels permutation142 permutation5
    mixedMoment B raw7717step1 raw7717step1Labels = mixedMoment B raw7717step2 raw7717step2Labels := by
      have ha : raw7717step2 = raw7717step1 := by apply Matrix.ext; unfold raw7717step2 raw7717step1; decide +kernel
      have hl : raw7717step1Labels = labelEmbedding8 ∘ raw7717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7717step1 raw7717step1Labels raw7717step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5106 node5106Labels := by rfl

def raw7718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7718step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7718step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7718 raw7718Labels = mixedMoment B node5106 node5106Labels := by
  calc
    mixedMoment B raw7718 raw7718Labels = mixedMoment B raw7718step0 raw7718step0Labels := by
      have hz : ∀ j, raw7718 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7718step0 = (fun i j => raw7718 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7718step0 raw7718; decide +kernel
      have hl : raw7718step0Labels = raw7718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7718 raw7718Labels permutation265 hz
    mixedMoment B raw7718step0 raw7718step0Labels = mixedMoment B raw7718step1 raw7718step1Labels := by
      have ha : raw7718step1 = (fun i j => raw7718step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7718step1 raw7718step0; decide +kernel
      have hl : raw7718step1Labels = raw7718step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7718step0 raw7718step0Labels permutation142 permutation5
    mixedMoment B raw7718step1 raw7718step1Labels = mixedMoment B raw7718step2 raw7718step2Labels := by
      have ha : raw7718step2 = raw7718step1 := by apply Matrix.ext; unfold raw7718step2 raw7718step1; decide +kernel
      have hl : raw7718step1Labels = labelEmbedding8 ∘ raw7718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7718step1 raw7718step1Labels raw7718step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5106 node5106Labels := by rfl

def raw7719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7719step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw7719step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7719step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw7719step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7719step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw7719step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7719 raw7719Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw7719 raw7719Labels = mixedMoment B raw7719step0 raw7719step0Labels := by
      have hz : ∀ j, raw7719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7719step0 = (fun i j => raw7719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7719step0 raw7719; decide +kernel
      have hl : raw7719step0Labels = raw7719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7719 raw7719Labels permutation346 hz
    mixedMoment B raw7719step0 raw7719step0Labels = mixedMoment B raw7719step1 raw7719step1Labels := by
      have hz : ∀ j, raw7719step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7719step1 = (fun i j => raw7719step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7719step1 raw7719step0; decide +kernel
      have hl : raw7719step1Labels = raw7719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7719step0 raw7719step0Labels permutation56 hz
    mixedMoment B raw7719step1 raw7719step1Labels = mixedMoment B raw7719step2 raw7719step2Labels := by
      have ha : raw7719step2 = (fun i j => raw7719step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7719step2 raw7719step1; decide +kernel
      have hl : raw7719step2Labels = raw7719step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7719step1 raw7719step1Labels permutation20 permutation4
    mixedMoment B raw7719step2 raw7719step2Labels = mixedMoment B raw7719step3 raw7719step3Labels := by
      have ha : raw7719step3 = -raw7719step2 := by apply Matrix.ext; change ∀ i j, raw7719step3 i j = -(raw7719step2 i j); unfold raw7719step3 raw7719step2; decide +kernel
      have hl : raw7719step3Labels = raw7719step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7719step3 raw7719step3Labels = mixedMoment B raw7719step4 raw7719step4Labels := by
      have ha : raw7719step4 = raw7719step3 := by apply Matrix.ext; unfold raw7719step4 raw7719step3; decide +kernel
      have hl : raw7719step3Labels = labelEmbedding7 ∘ raw7719step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7719step3 raw7719step3Labels raw7719step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw7720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7720step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7720step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7720 raw7720Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw7720 raw7720Labels = mixedMoment B raw7720step0 raw7720step0Labels := by
      have hz : ∀ j, raw7720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7720step0 = (fun i j => raw7720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7720step0 raw7720; decide +kernel
      have hl : raw7720step0Labels = raw7720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7720 raw7720Labels permutation346 hz
    mixedMoment B raw7720step0 raw7720step0Labels = mixedMoment B raw7720step1 raw7720step1Labels := by
      have hz : ∀ j, raw7720step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7720step1 = (fun i j => raw7720step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7720step1 raw7720step0; decide +kernel
      have hl : raw7720step1Labels = raw7720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7720step0 raw7720step0Labels permutation56 hz
    mixedMoment B raw7720step1 raw7720step1Labels = mixedMoment B raw7720step2 raw7720step2Labels := by
      have ha : raw7720step2 = (fun i j => raw7720step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7720step2 raw7720step1; decide +kernel
      have hl : raw7720step2Labels = raw7720step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7720step1 raw7720step1Labels permutation23 permutation6
    mixedMoment B raw7720step2 raw7720step2Labels = mixedMoment B raw7720step3 raw7720step3Labels := by
      have ha : raw7720step3 = raw7720step2 := by apply Matrix.ext; unfold raw7720step3 raw7720step2; decide +kernel
      have hl : raw7720step2Labels = labelEmbedding9 ∘ raw7720step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7720step2 raw7720step2Labels raw7720step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw7721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7721step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 1, -3], ![2, -3, 1]]
def raw7721step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7721step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw7721step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7721 raw7721Labels = mixedMoment B node4626 node4626Labels := by
  calc
    mixedMoment B raw7721 raw7721Labels = mixedMoment B raw7721step0 raw7721step0Labels := by
      have hz : ∀ j, raw7721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7721step0 = (fun i j => raw7721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7721step0 raw7721; decide +kernel
      have hl : raw7721step0Labels = raw7721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7721 raw7721Labels permutation434 hz
    mixedMoment B raw7721step0 raw7721step0Labels = mixedMoment B raw7721step1 raw7721step1Labels := by
      have hz : ∀ j, raw7721step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7721step1 = (fun i j => raw7721step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7721step1 raw7721step0; decide +kernel
      have hl : raw7721step1Labels = raw7721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7721step0 raw7721step0Labels permutation80 hz
    mixedMoment B raw7721step1 raw7721step1Labels = mixedMoment B raw7721step2 raw7721step2Labels := by
      have hz : ∀ j, raw7721step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7721step2 = (fun i j => raw7721step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7721step2 raw7721step1; decide +kernel
      have hl : raw7721step2Labels = raw7721step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7721step1 raw7721step1Labels permutation14 hz
    mixedMoment B raw7721step2 raw7721step2Labels = mixedMoment B raw7721step3 raw7721step3Labels := by
      have ha : raw7721step3 = (fun i j => raw7721step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7721step3 raw7721step2; decide +kernel
      have hl : raw7721step3Labels = raw7721step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7721step2 raw7721step2Labels permutation3 permutation2
    _ = mixedMoment B node4626 node4626Labels := by rfl

def raw7722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw7722step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7722 raw7722Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw7722 raw7722Labels = mixedMoment B raw7722step0 raw7722step0Labels := by
      have hz : ∀ j, raw7722 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7722step0 = (fun i j => raw7722 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7722step0 raw7722; decide +kernel
      have hl : raw7722step0Labels = raw7722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7722 raw7722Labels permutation434 hz
    mixedMoment B raw7722step0 raw7722step0Labels = mixedMoment B raw7722step1 raw7722step1Labels := by
      have hz : ∀ j, raw7722step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7722step1 = (fun i j => raw7722step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7722step1 raw7722step0; decide +kernel
      have hl : raw7722step1Labels = raw7722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7722step0 raw7722step0Labels permutation80 hz
    mixedMoment B raw7722step1 raw7722step1Labels = mixedMoment B raw7722step2 raw7722step2Labels := by
      have ha : raw7722step2 = (fun i j => raw7722step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7722step2 raw7722step1; decide +kernel
      have hl : raw7722step2Labels = raw7722step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7722step1 raw7722step1Labels permutation9 permutation2
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw7723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw7723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7723 raw7723Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw7723 raw7723Labels = mixedMoment B raw7723step0 raw7723step0Labels := by
      have hz : ∀ j, raw7723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7723step0 = (fun i j => raw7723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7723step0 raw7723; decide +kernel
      have hl : raw7723step0Labels = raw7723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7723 raw7723Labels permutation434 hz
    mixedMoment B raw7723step0 raw7723step0Labels = mixedMoment B raw7723step1 raw7723step1Labels := by
      have hz : ∀ j, raw7723step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7723step1 = (fun i j => raw7723step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7723step1 raw7723step0; decide +kernel
      have hl : raw7723step1Labels = raw7723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7723step0 raw7723step0Labels permutation56 hz
    mixedMoment B raw7723step1 raw7723step1Labels = mixedMoment B raw7723step2 raw7723step2Labels := by
      have ha : raw7723step2 = (fun i j => raw7723step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7723step2 raw7723step1; decide +kernel
      have hl : raw7723step2Labels = raw7723step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7723step1 raw7723step1Labels permutation9 permutation2
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw7724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw7724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7724 raw7724Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw7724 raw7724Labels = mixedMoment B raw7724step0 raw7724step0Labels := by
      have hz : ∀ j, raw7724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7724step0 = (fun i j => raw7724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7724step0 raw7724; decide +kernel
      have hl : raw7724step0Labels = raw7724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7724 raw7724Labels permutation346 hz
    mixedMoment B raw7724step0 raw7724step0Labels = mixedMoment B raw7724step1 raw7724step1Labels := by
      have hz : ∀ j, raw7724step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7724step1 = (fun i j => raw7724step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7724step1 raw7724step0; decide +kernel
      have hl : raw7724step1Labels = raw7724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7724step0 raw7724step0Labels permutation56 hz
    mixedMoment B raw7724step1 raw7724step1Labels = mixedMoment B raw7724step2 raw7724step2Labels := by
      have ha : raw7724step2 = (fun i j => raw7724step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7724step2 raw7724step1; decide +kernel
      have hl : raw7724step2Labels = raw7724step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7724step1 raw7724step1Labels permutation9 permutation2
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw7725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7725step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 1, -3], ![1, -2, 1]]
def raw7725step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7725step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7725step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7725 raw7725Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw7725 raw7725Labels = mixedMoment B raw7725step0 raw7725step0Labels := by
      have hz : ∀ j, raw7725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7725step0 = (fun i j => raw7725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7725step0 raw7725; decide +kernel
      have hl : raw7725step0Labels = raw7725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7725 raw7725Labels permutation434 hz
    mixedMoment B raw7725step0 raw7725step0Labels = mixedMoment B raw7725step1 raw7725step1Labels := by
      have hz : ∀ j, raw7725step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7725step1 = (fun i j => raw7725step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7725step1 raw7725step0; decide +kernel
      have hl : raw7725step1Labels = raw7725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7725step0 raw7725step0Labels permutation80 hz
    mixedMoment B raw7725step1 raw7725step1Labels = mixedMoment B raw7725step2 raw7725step2Labels := by
      have hz : ∀ j, raw7725step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7725step2 = (fun i j => raw7725step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7725step2 raw7725step1; decide +kernel
      have hl : raw7725step2Labels = raw7725step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7725step1 raw7725step1Labels permutation14 hz
    mixedMoment B raw7725step2 raw7725step2Labels = mixedMoment B raw7725step3 raw7725step3Labels := by
      have ha : raw7725step3 = (fun i j => raw7725step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7725step3 raw7725step2; decide +kernel
      have hl : raw7725step3Labels = raw7725step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7725step2 raw7725step2Labels permutation3 permutation2
    _ = mixedMoment B node5305 node5305Labels := by rfl

def raw7726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7726step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw7726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7726step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw7726step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7726step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw7726step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7726 raw7726Labels = mixedMoment B node4509 node4509Labels := by
  calc
    mixedMoment B raw7726 raw7726Labels = mixedMoment B raw7726step0 raw7726step0Labels := by
      have hz : ∀ j, raw7726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7726step0 = (fun i j => raw7726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7726step0 raw7726; decide +kernel
      have hl : raw7726step0Labels = raw7726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7726 raw7726Labels permutation434 hz
    mixedMoment B raw7726step0 raw7726step0Labels = mixedMoment B raw7726step1 raw7726step1Labels := by
      have hz : ∀ j, raw7726step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7726step1 = (fun i j => raw7726step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7726step1 raw7726step0; decide +kernel
      have hl : raw7726step1Labels = raw7726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7726step0 raw7726step0Labels permutation80 hz
    mixedMoment B raw7726step1 raw7726step1Labels = mixedMoment B raw7726step2 raw7726step2Labels := by
      have hz : ∀ j, raw7726step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7726step2 = (fun i j => raw7726step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7726step2 raw7726step1; decide +kernel
      have hl : raw7726step2Labels = raw7726step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7726step1 raw7726step1Labels permutation14 hz
    mixedMoment B raw7726step2 raw7726step2Labels = mixedMoment B raw7726step3 raw7726step3Labels := by
      have ha : raw7726step3 = (fun i j => raw7726step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7726step3 raw7726step2; decide +kernel
      have hl : raw7726step3Labels = raw7726step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7726step2 raw7726step2Labels permutation7 permutation5
    mixedMoment B raw7726step3 raw7726step3Labels = mixedMoment B raw7726step4 raw7726step4Labels := by
      have ha : raw7726step4 = raw7726step3 := by apply Matrix.ext; unfold raw7726step4 raw7726step3; decide +kernel
      have hl : raw7726step3Labels = labelEmbedding8 ∘ raw7726step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7726step3 raw7726step3Labels raw7726step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4509 node4509Labels := by rfl

def raw7727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7727step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7727step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7727 raw7727Labels = mixedMoment B node4504 node4504Labels := by
  calc
    mixedMoment B raw7727 raw7727Labels = mixedMoment B raw7727step0 raw7727step0Labels := by
      have hz : ∀ j, raw7727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7727step0 = (fun i j => raw7727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7727step0 raw7727; decide +kernel
      have hl : raw7727step0Labels = raw7727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7727 raw7727Labels permutation434 hz
    mixedMoment B raw7727step0 raw7727step0Labels = mixedMoment B raw7727step1 raw7727step1Labels := by
      have hz : ∀ j, raw7727step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7727step1 = (fun i j => raw7727step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7727step1 raw7727step0; decide +kernel
      have hl : raw7727step1Labels = raw7727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7727step0 raw7727step0Labels permutation80 hz
    mixedMoment B raw7727step1 raw7727step1Labels = mixedMoment B raw7727step2 raw7727step2Labels := by
      have ha : raw7727step2 = (fun i j => raw7727step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7727step2 raw7727step1; decide +kernel
      have hl : raw7727step2Labels = raw7727step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7727step1 raw7727step1Labels permutation28 permutation5
    mixedMoment B raw7727step2 raw7727step2Labels = mixedMoment B raw7727step3 raw7727step3Labels := by
      have ha : raw7727step3 = raw7727step2 := by apply Matrix.ext; unfold raw7727step3 raw7727step2; decide +kernel
      have hl : raw7727step2Labels = labelEmbedding8 ∘ raw7727step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7727step2 raw7727step2Labels raw7727step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4504 node4504Labels := by rfl

def raw7728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7728step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7728step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7728step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7728 raw7728Labels = mixedMoment B node4504 node4504Labels := by
  calc
    mixedMoment B raw7728 raw7728Labels = mixedMoment B raw7728step0 raw7728step0Labels := by
      have hz : ∀ j, raw7728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7728step0 = (fun i j => raw7728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7728step0 raw7728; decide +kernel
      have hl : raw7728step0Labels = raw7728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7728 raw7728Labels permutation434 hz
    mixedMoment B raw7728step0 raw7728step0Labels = mixedMoment B raw7728step1 raw7728step1Labels := by
      have hz : ∀ j, raw7728step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7728step1 = (fun i j => raw7728step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7728step1 raw7728step0; decide +kernel
      have hl : raw7728step1Labels = raw7728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7728step0 raw7728step0Labels permutation56 hz
    mixedMoment B raw7728step1 raw7728step1Labels = mixedMoment B raw7728step2 raw7728step2Labels := by
      have ha : raw7728step2 = (fun i j => raw7728step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7728step2 raw7728step1; decide +kernel
      have hl : raw7728step2Labels = raw7728step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7728step1 raw7728step1Labels permutation28 permutation5
    mixedMoment B raw7728step2 raw7728step2Labels = mixedMoment B raw7728step3 raw7728step3Labels := by
      have ha : raw7728step3 = raw7728step2 := by apply Matrix.ext; unfold raw7728step3 raw7728step2; decide +kernel
      have hl : raw7728step2Labels = labelEmbedding8 ∘ raw7728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7728step2 raw7728step2Labels raw7728step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4504 node4504Labels := by rfl

def raw7729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7729step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7729step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7729step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7729 raw7729Labels = mixedMoment B node4504 node4504Labels := by
  calc
    mixedMoment B raw7729 raw7729Labels = mixedMoment B raw7729step0 raw7729step0Labels := by
      have hz : ∀ j, raw7729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7729step0 = (fun i j => raw7729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7729step0 raw7729; decide +kernel
      have hl : raw7729step0Labels = raw7729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7729 raw7729Labels permutation346 hz
    mixedMoment B raw7729step0 raw7729step0Labels = mixedMoment B raw7729step1 raw7729step1Labels := by
      have hz : ∀ j, raw7729step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7729step1 = (fun i j => raw7729step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7729step1 raw7729step0; decide +kernel
      have hl : raw7729step1Labels = raw7729step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7729step0 raw7729step0Labels permutation56 hz
    mixedMoment B raw7729step1 raw7729step1Labels = mixedMoment B raw7729step2 raw7729step2Labels := by
      have ha : raw7729step2 = (fun i j => raw7729step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7729step2 raw7729step1; decide +kernel
      have hl : raw7729step2Labels = raw7729step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7729step1 raw7729step1Labels permutation28 permutation5
    mixedMoment B raw7729step2 raw7729step2Labels = mixedMoment B raw7729step3 raw7729step3Labels := by
      have ha : raw7729step3 = raw7729step2 := by apply Matrix.ext; unfold raw7729step3 raw7729step2; decide +kernel
      have hl : raw7729step2Labels = labelEmbedding8 ∘ raw7729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7729step2 raw7729step2Labels raw7729step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4504 node4504Labels := by rfl

def raw7730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7730step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7730step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 3, -3], ![3, -4, 1]]
def raw7730step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7730step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw7730step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7730step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw7730step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7730 raw7730Labels = mixedMoment B node4508 node4508Labels := by
  calc
    mixedMoment B raw7730 raw7730Labels = mixedMoment B raw7730step0 raw7730step0Labels := by
      have hz : ∀ j, raw7730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7730step0 = (fun i j => raw7730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7730step0 raw7730; decide +kernel
      have hl : raw7730step0Labels = raw7730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7730 raw7730Labels permutation434 hz
    mixedMoment B raw7730step0 raw7730step0Labels = mixedMoment B raw7730step1 raw7730step1Labels := by
      have hz : ∀ j, raw7730step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7730step1 = (fun i j => raw7730step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7730step1 raw7730step0; decide +kernel
      have hl : raw7730step1Labels = raw7730step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7730step0 raw7730step0Labels permutation80 hz
    mixedMoment B raw7730step1 raw7730step1Labels = mixedMoment B raw7730step2 raw7730step2Labels := by
      have hz : ∀ j, raw7730step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7730step2 = (fun i j => raw7730step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7730step2 raw7730step1; decide +kernel
      have hl : raw7730step2Labels = raw7730step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7730step1 raw7730step1Labels permutation14 hz
    mixedMoment B raw7730step2 raw7730step2Labels = mixedMoment B raw7730step3 raw7730step3Labels := by
      have ha : raw7730step3 = (fun i j => raw7730step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7730step3 raw7730step2; decide +kernel
      have hl : raw7730step3Labels = raw7730step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7730step2 raw7730step2Labels permutation6 permutation5
    mixedMoment B raw7730step3 raw7730step3Labels = mixedMoment B raw7730step4 raw7730step4Labels := by
      have ha : raw7730step4 = raw7730step3 := by apply Matrix.ext; unfold raw7730step4 raw7730step3; decide +kernel
      have hl : raw7730step3Labels = labelEmbedding8 ∘ raw7730step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7730step3 raw7730step3Labels raw7730step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4508 node4508Labels := by rfl

def raw7731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7731step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7731 raw7731Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw7731 raw7731Labels = mixedMoment B raw7731step0 raw7731step0Labels := by
      have hz : ∀ j, raw7731 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7731step0 = (fun i j => raw7731 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7731step0 raw7731; decide +kernel
      have hl : raw7731step0Labels = raw7731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7731 raw7731Labels permutation434 hz
    mixedMoment B raw7731step0 raw7731step0Labels = mixedMoment B raw7731step1 raw7731step1Labels := by
      have hz : ∀ j, raw7731step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7731step1 = (fun i j => raw7731step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7731step1 raw7731step0; decide +kernel
      have hl : raw7731step1Labels = raw7731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7731step0 raw7731step0Labels permutation80 hz
    mixedMoment B raw7731step1 raw7731step1Labels = mixedMoment B raw7731step2 raw7731step2Labels := by
      have ha : raw7731step2 = (fun i j => raw7731step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7731step2 raw7731step1; decide +kernel
      have hl : raw7731step2Labels = raw7731step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7731step1 raw7731step1Labels permutation23 permutation6
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw7732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7732step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7732step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7732 raw7732Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw7732 raw7732Labels = mixedMoment B raw7732step0 raw7732step0Labels := by
      have hz : ∀ j, raw7732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7732step0 = (fun i j => raw7732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7732step0 raw7732; decide +kernel
      have hl : raw7732step0Labels = raw7732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7732 raw7732Labels permutation434 hz
    mixedMoment B raw7732step0 raw7732step0Labels = mixedMoment B raw7732step1 raw7732step1Labels := by
      have hz : ∀ j, raw7732step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7732step1 = (fun i j => raw7732step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7732step1 raw7732step0; decide +kernel
      have hl : raw7732step1Labels = raw7732step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7732step0 raw7732step0Labels permutation56 hz
    mixedMoment B raw7732step1 raw7732step1Labels = mixedMoment B raw7732step2 raw7732step2Labels := by
      have ha : raw7732step2 = (fun i j => raw7732step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7732step2 raw7732step1; decide +kernel
      have hl : raw7732step2Labels = raw7732step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7732step1 raw7732step1Labels permutation23 permutation6
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw7733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7733step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7733 raw7733Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw7733 raw7733Labels = mixedMoment B raw7733step0 raw7733step0Labels := by
      have hz : ∀ j, raw7733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7733step0 = (fun i j => raw7733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7733step0 raw7733; decide +kernel
      have hl : raw7733step0Labels = raw7733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7733 raw7733Labels permutation346 hz
    mixedMoment B raw7733step0 raw7733step0Labels = mixedMoment B raw7733step1 raw7733step1Labels := by
      have hz : ∀ j, raw7733step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7733step1 = (fun i j => raw7733step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7733step1 raw7733step0; decide +kernel
      have hl : raw7733step1Labels = raw7733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7733step0 raw7733step0Labels permutation56 hz
    mixedMoment B raw7733step1 raw7733step1Labels = mixedMoment B raw7733step2 raw7733step2Labels := by
      have ha : raw7733step2 = (fun i j => raw7733step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7733step2 raw7733step1; decide +kernel
      have hl : raw7733step2Labels = raw7733step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7733step1 raw7733step1Labels permutation23 permutation6
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw7734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7734step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7734step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7734step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7734step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]
def raw7734step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7734step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw7734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7734 raw7734Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw7734 raw7734Labels = mixedMoment B raw7734step0 raw7734step0Labels := by
      have hz : ∀ j, raw7734 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7734step0 = (fun i j => raw7734 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7734step0 raw7734; decide +kernel
      have hl : raw7734step0Labels = raw7734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7734 raw7734Labels permutation434 hz
    mixedMoment B raw7734step0 raw7734step0Labels = mixedMoment B raw7734step1 raw7734step1Labels := by
      have hz : ∀ j, raw7734step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7734step1 = (fun i j => raw7734step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7734step1 raw7734step0; decide +kernel
      have hl : raw7734step1Labels = raw7734step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7734step0 raw7734step0Labels permutation80 hz
    mixedMoment B raw7734step1 raw7734step1Labels = mixedMoment B raw7734step2 raw7734step2Labels := by
      have hz : ∀ j, raw7734step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7734step2 = (fun i j => raw7734step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7734step2 raw7734step1; decide +kernel
      have hl : raw7734step2Labels = raw7734step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7734step1 raw7734step1Labels permutation14 hz
    mixedMoment B raw7734step2 raw7734step2Labels = mixedMoment B raw7734step3 raw7734step3Labels := by
      have ha : raw7734step3 = (fun i j => raw7734step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7734step3 raw7734step2; decide +kernel
      have hl : raw7734step3Labels = raw7734step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7734step2 raw7734step2Labels permutation5 permutation6
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw7735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7735step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7735step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7735step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![1, -2, 1]]
def raw7735step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7735step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw7735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7735 raw7735Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw7735 raw7735Labels = mixedMoment B raw7735step0 raw7735step0Labels := by
      have hz : ∀ j, raw7735 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7735step0 = (fun i j => raw7735 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7735step0 raw7735; decide +kernel
      have hl : raw7735step0Labels = raw7735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7735 raw7735Labels permutation434 hz
    mixedMoment B raw7735step0 raw7735step0Labels = mixedMoment B raw7735step1 raw7735step1Labels := by
      have hz : ∀ j, raw7735step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7735step1 = (fun i j => raw7735step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7735step1 raw7735step0; decide +kernel
      have hl : raw7735step1Labels = raw7735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7735step0 raw7735step0Labels permutation80 hz
    mixedMoment B raw7735step1 raw7735step1Labels = mixedMoment B raw7735step2 raw7735step2Labels := by
      have hz : ∀ j, raw7735step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7735step2 = (fun i j => raw7735step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7735step2 raw7735step1; decide +kernel
      have hl : raw7735step2Labels = raw7735step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7735step1 raw7735step1Labels permutation14 hz
    mixedMoment B raw7735step2 raw7735step2Labels = mixedMoment B raw7735step3 raw7735step3Labels := by
      have ha : raw7735step3 = (fun i j => raw7735step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7735step3 raw7735step2; decide +kernel
      have hl : raw7735step3Labels = raw7735step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7735step2 raw7735step2Labels permutation5 permutation6
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw7736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7736step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw7736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7736 raw7736Labels = mixedMoment B node1287 node1287Labels := by
  calc
    mixedMoment B raw7736 raw7736Labels = mixedMoment B raw7736step0 raw7736step0Labels := by
      have hz : ∀ j, raw7736 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7736step0 = (fun i j => raw7736 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7736step0 raw7736; decide +kernel
      have hl : raw7736step0Labels = raw7736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7736 raw7736Labels permutation434 hz
    mixedMoment B raw7736step0 raw7736step0Labels = mixedMoment B raw7736step1 raw7736step1Labels := by
      have hz : ∀ j, raw7736step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7736step1 = (fun i j => raw7736step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7736step1 raw7736step0; decide +kernel
      have hl : raw7736step1Labels = raw7736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7736step0 raw7736step0Labels permutation80 hz
    mixedMoment B raw7736step1 raw7736step1Labels = mixedMoment B raw7736step2 raw7736step2Labels := by
      have ha : raw7736step2 = (fun i j => raw7736step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7736step2 raw7736step1; decide +kernel
      have hl : raw7736step2Labels = raw7736step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7736step1 raw7736step1Labels permutation10 permutation3
    _ = mixedMoment B node1287 node1287Labels := by rfl

def raw7737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7737step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7737 raw7737Labels = mixedMoment B node2725 node2725Labels := by
  calc
    mixedMoment B raw7737 raw7737Labels = mixedMoment B raw7737step0 raw7737step0Labels := by
      have hz : ∀ j, raw7737 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7737step0 = (fun i j => raw7737 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7737step0 raw7737; decide +kernel
      have hl : raw7737step0Labels = raw7737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7737 raw7737Labels permutation434 hz
    mixedMoment B raw7737step0 raw7737step0Labels = mixedMoment B raw7737step1 raw7737step1Labels := by
      have ha : raw7737step1 = (fun i j => raw7737step0 (permutation119 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7737step1 raw7737step0; decide +kernel
      have hl : raw7737step1Labels = raw7737step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7737step0 raw7737step0Labels permutation119 permutation6
    _ = mixedMoment B node2725 node2725Labels := by rfl

def raw7738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7738step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7738 raw7738Labels = mixedMoment B node2725 node2725Labels := by
  calc
    mixedMoment B raw7738 raw7738Labels = mixedMoment B raw7738step0 raw7738step0Labels := by
      have hz : ∀ j, raw7738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7738step0 = (fun i j => raw7738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7738step0 raw7738; decide +kernel
      have hl : raw7738step0Labels = raw7738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7738 raw7738Labels permutation346 hz
    mixedMoment B raw7738step0 raw7738step0Labels = mixedMoment B raw7738step1 raw7738step1Labels := by
      have ha : raw7738step1 = (fun i j => raw7738step0 (permutation119 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7738step1 raw7738step0; decide +kernel
      have hl : raw7738step1Labels = raw7738step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7738step0 raw7738step0Labels permutation119 permutation6
    _ = mixedMoment B node2725 node2725Labels := by rfl

def raw7739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7739step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7739step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7739 raw7739Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw7739 raw7739Labels = mixedMoment B raw7739step0 raw7739step0Labels := by
      have hz : ∀ j, raw7739 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7739step0 = (fun i j => raw7739 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7739step0 raw7739; decide +kernel
      have hl : raw7739step0Labels = raw7739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7739 raw7739Labels permutation434 hz
    mixedMoment B raw7739step0 raw7739step0Labels = mixedMoment B raw7739step1 raw7739step1Labels := by
      have hz : ∀ j, raw7739step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7739step1 = (fun i j => raw7739step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7739step1 raw7739step0; decide +kernel
      have hl : raw7739step1Labels = raw7739step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7739step0 raw7739step0Labels permutation80 hz
    mixedMoment B raw7739step1 raw7739step1Labels = mixedMoment B raw7739step2 raw7739step2Labels := by
      have ha : raw7739step2 = (fun i j => raw7739step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7739step2 raw7739step1; decide +kernel
      have hl : raw7739step2Labels = raw7739step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7739step1 raw7739step1Labels permutation23 permutation6
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw7740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7740step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7740step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7740step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7740 raw7740Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw7740 raw7740Labels = mixedMoment B raw7740step0 raw7740step0Labels := by
      have hz : ∀ j, raw7740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7740step0 = (fun i j => raw7740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7740step0 raw7740; decide +kernel
      have hl : raw7740step0Labels = raw7740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7740 raw7740Labels permutation434 hz
    mixedMoment B raw7740step0 raw7740step0Labels = mixedMoment B raw7740step1 raw7740step1Labels := by
      have hz : ∀ j, raw7740step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7740step1 = (fun i j => raw7740step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7740step1 raw7740step0; decide +kernel
      have hl : raw7740step1Labels = raw7740step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7740step0 raw7740step0Labels permutation80 hz
    mixedMoment B raw7740step1 raw7740step1Labels = mixedMoment B raw7740step2 raw7740step2Labels := by
      have ha : raw7740step2 = (fun i j => raw7740step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7740step2 raw7740step1; decide +kernel
      have hl : raw7740step2Labels = raw7740step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7740step1 raw7740step1Labels permutation23 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw7741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7741step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7741step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw7741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7741 raw7741Labels = mixedMoment B node1287 node1287Labels := by
  calc
    mixedMoment B raw7741 raw7741Labels = mixedMoment B raw7741step0 raw7741step0Labels := by
      have hz : ∀ j, raw7741 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7741step0 = (fun i j => raw7741 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7741step0 raw7741; decide +kernel
      have hl : raw7741step0Labels = raw7741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7741 raw7741Labels permutation434 hz
    mixedMoment B raw7741step0 raw7741step0Labels = mixedMoment B raw7741step1 raw7741step1Labels := by
      have hz : ∀ j, raw7741step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7741step1 = (fun i j => raw7741step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7741step1 raw7741step0; decide +kernel
      have hl : raw7741step1Labels = raw7741step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7741step0 raw7741step0Labels permutation56 hz
    mixedMoment B raw7741step1 raw7741step1Labels = mixedMoment B raw7741step2 raw7741step2Labels := by
      have ha : raw7741step2 = (fun i j => raw7741step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7741step2 raw7741step1; decide +kernel
      have hl : raw7741step2Labels = raw7741step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7741step1 raw7741step1Labels permutation10 permutation3
    _ = mixedMoment B node1287 node1287Labels := by rfl

def raw7742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7742step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7742 raw7742Labels = mixedMoment B node2725 node2725Labels := by
  calc
    mixedMoment B raw7742 raw7742Labels = mixedMoment B raw7742step0 raw7742step0Labels := by
      have hz : ∀ j, raw7742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7742step0 = (fun i j => raw7742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7742step0 raw7742; decide +kernel
      have hl : raw7742step0Labels = raw7742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7742 raw7742Labels permutation434 hz
    mixedMoment B raw7742step0 raw7742step0Labels = mixedMoment B raw7742step1 raw7742step1Labels := by
      have ha : raw7742step1 = (fun i j => raw7742step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7742step1 raw7742step0; decide +kernel
      have hl : raw7742step1Labels = raw7742step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7742step0 raw7742step0Labels permutation113 permutation6
    _ = mixedMoment B node2725 node2725Labels := by rfl

def raw7743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7743step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7743 raw7743Labels = mixedMoment B node2725 node2725Labels := by
  calc
    mixedMoment B raw7743 raw7743Labels = mixedMoment B raw7743step0 raw7743step0Labels := by
      have hz : ∀ j, raw7743 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7743step0 = (fun i j => raw7743 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7743step0 raw7743; decide +kernel
      have hl : raw7743step0Labels = raw7743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7743 raw7743Labels permutation265 hz
    mixedMoment B raw7743step0 raw7743step0Labels = mixedMoment B raw7743step1 raw7743step1Labels := by
      have ha : raw7743step1 = (fun i j => raw7743step0 (permutation119 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7743step1 raw7743step0; decide +kernel
      have hl : raw7743step1Labels = raw7743step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7743step0 raw7743step0Labels permutation119 permutation6
    _ = mixedMoment B node2725 node2725Labels := by rfl

def raw7744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7744step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7744step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7744 raw7744Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw7744 raw7744Labels = mixedMoment B raw7744step0 raw7744step0Labels := by
      have hz : ∀ j, raw7744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7744step0 = (fun i j => raw7744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7744step0 raw7744; decide +kernel
      have hl : raw7744step0Labels = raw7744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7744 raw7744Labels permutation434 hz
    mixedMoment B raw7744step0 raw7744step0Labels = mixedMoment B raw7744step1 raw7744step1Labels := by
      have hz : ∀ j, raw7744step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7744step1 = (fun i j => raw7744step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7744step1 raw7744step0; decide +kernel
      have hl : raw7744step1Labels = raw7744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7744step0 raw7744step0Labels permutation56 hz
    mixedMoment B raw7744step1 raw7744step1Labels = mixedMoment B raw7744step2 raw7744step2Labels := by
      have ha : raw7744step2 = (fun i j => raw7744step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7744step2 raw7744step1; decide +kernel
      have hl : raw7744step2Labels = raw7744step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7744step1 raw7744step1Labels permutation23 permutation6
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw7745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7745step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7745step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7745 raw7745Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw7745 raw7745Labels = mixedMoment B raw7745step0 raw7745step0Labels := by
      have hz : ∀ j, raw7745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7745step0 = (fun i j => raw7745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7745step0 raw7745; decide +kernel
      have hl : raw7745step0Labels = raw7745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7745 raw7745Labels permutation434 hz
    mixedMoment B raw7745step0 raw7745step0Labels = mixedMoment B raw7745step1 raw7745step1Labels := by
      have hz : ∀ j, raw7745step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7745step1 = (fun i j => raw7745step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7745step1 raw7745step0; decide +kernel
      have hl : raw7745step1Labels = raw7745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7745step0 raw7745step0Labels permutation56 hz
    mixedMoment B raw7745step1 raw7745step1Labels = mixedMoment B raw7745step2 raw7745step2Labels := by
      have ha : raw7745step2 = (fun i j => raw7745step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7745step2 raw7745step1; decide +kernel
      have hl : raw7745step2Labels = raw7745step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7745step1 raw7745step1Labels permutation23 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw7746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7746step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7746step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw7746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7746 raw7746Labels = mixedMoment B node1287 node1287Labels := by
  calc
    mixedMoment B raw7746 raw7746Labels = mixedMoment B raw7746step0 raw7746step0Labels := by
      have hz : ∀ j, raw7746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7746step0 = (fun i j => raw7746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7746step0 raw7746; decide +kernel
      have hl : raw7746step0Labels = raw7746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7746 raw7746Labels permutation346 hz
    mixedMoment B raw7746step0 raw7746step0Labels = mixedMoment B raw7746step1 raw7746step1Labels := by
      have hz : ∀ j, raw7746step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7746step1 = (fun i j => raw7746step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7746step1 raw7746step0; decide +kernel
      have hl : raw7746step1Labels = raw7746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7746step0 raw7746step0Labels permutation56 hz
    mixedMoment B raw7746step1 raw7746step1Labels = mixedMoment B raw7746step2 raw7746step2Labels := by
      have ha : raw7746step2 = (fun i j => raw7746step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7746step2 raw7746step1; decide +kernel
      have hl : raw7746step2Labels = raw7746step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7746step1 raw7746step1Labels permutation10 permutation3
    _ = mixedMoment B node1287 node1287Labels := by rfl

def raw7747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7747step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7747 raw7747Labels = mixedMoment B node2725 node2725Labels := by
  calc
    mixedMoment B raw7747 raw7747Labels = mixedMoment B raw7747step0 raw7747step0Labels := by
      have hz : ∀ j, raw7747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7747step0 = (fun i j => raw7747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7747step0 raw7747; decide +kernel
      have hl : raw7747step0Labels = raw7747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7747 raw7747Labels permutation346 hz
    mixedMoment B raw7747step0 raw7747step0Labels = mixedMoment B raw7747step1 raw7747step1Labels := by
      have ha : raw7747step1 = (fun i j => raw7747step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7747step1 raw7747step0; decide +kernel
      have hl : raw7747step1Labels = raw7747step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7747step0 raw7747step0Labels permutation113 permutation6
    _ = mixedMoment B node2725 node2725Labels := by rfl

def raw7748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7748step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7748 raw7748Labels = mixedMoment B node2725 node2725Labels := by
  calc
    mixedMoment B raw7748 raw7748Labels = mixedMoment B raw7748step0 raw7748step0Labels := by
      have hz : ∀ j, raw7748 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7748step0 = (fun i j => raw7748 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7748step0 raw7748; decide +kernel
      have hl : raw7748step0Labels = raw7748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7748 raw7748Labels permutation265 hz
    mixedMoment B raw7748step0 raw7748step0Labels = mixedMoment B raw7748step1 raw7748step1Labels := by
      have ha : raw7748step1 = (fun i j => raw7748step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7748step1 raw7748step0; decide +kernel
      have hl : raw7748step1Labels = raw7748step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7748step0 raw7748step0Labels permutation113 permutation6
    _ = mixedMoment B node2725 node2725Labels := by rfl

def raw7749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7749step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7749step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7749 raw7749Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw7749 raw7749Labels = mixedMoment B raw7749step0 raw7749step0Labels := by
      have hz : ∀ j, raw7749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7749step0 = (fun i j => raw7749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7749step0 raw7749; decide +kernel
      have hl : raw7749step0Labels = raw7749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7749 raw7749Labels permutation346 hz
    mixedMoment B raw7749step0 raw7749step0Labels = mixedMoment B raw7749step1 raw7749step1Labels := by
      have hz : ∀ j, raw7749step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7749step1 = (fun i j => raw7749step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7749step1 raw7749step0; decide +kernel
      have hl : raw7749step1Labels = raw7749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7749step0 raw7749step0Labels permutation56 hz
    mixedMoment B raw7749step1 raw7749step1Labels = mixedMoment B raw7749step2 raw7749step2Labels := by
      have ha : raw7749step2 = (fun i j => raw7749step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7749step2 raw7749step1; decide +kernel
      have hl : raw7749step2Labels = raw7749step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7749step1 raw7749step1Labels permutation23 permutation6
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw7750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7750Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7750step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7750step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7750 raw7750Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw7750 raw7750Labels = mixedMoment B raw7750step0 raw7750step0Labels := by
      have hz : ∀ j, raw7750 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7750step0 = (fun i j => raw7750 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7750step0 raw7750; decide +kernel
      have hl : raw7750step0Labels = raw7750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7750 raw7750Labels permutation346 hz
    mixedMoment B raw7750step0 raw7750step0Labels = mixedMoment B raw7750step1 raw7750step1Labels := by
      have hz : ∀ j, raw7750step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7750step1 = (fun i j => raw7750step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7750step1 raw7750step0; decide +kernel
      have hl : raw7750step1Labels = raw7750step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7750step0 raw7750step0Labels permutation56 hz
    mixedMoment B raw7750step1 raw7750step1Labels = mixedMoment B raw7750step2 raw7750step2Labels := by
      have ha : raw7750step2 = (fun i j => raw7750step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7750step2 raw7750step1; decide +kernel
      have hl : raw7750step2Labels = raw7750step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7750step1 raw7750step1Labels permutation23 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw7751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7751Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7751step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7751step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7751step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 1, -3], ![2, -3, 1]]
def raw7751step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7751step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw7751step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7751 raw7751Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw7751 raw7751Labels = mixedMoment B raw7751step0 raw7751step0Labels := by
      have hz : ∀ j, raw7751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7751step0 = (fun i j => raw7751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7751step0 raw7751; decide +kernel
      have hl : raw7751step0Labels = raw7751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7751 raw7751Labels permutation434 hz
    mixedMoment B raw7751step0 raw7751step0Labels = mixedMoment B raw7751step1 raw7751step1Labels := by
      have hz : ∀ j, raw7751step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7751step1 = (fun i j => raw7751step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7751step1 raw7751step0; decide +kernel
      have hl : raw7751step1Labels = raw7751step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7751step0 raw7751step0Labels permutation80 hz
    mixedMoment B raw7751step1 raw7751step1Labels = mixedMoment B raw7751step2 raw7751step2Labels := by
      have hz : ∀ j, raw7751step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7751step2 = (fun i j => raw7751step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7751step2 raw7751step1; decide +kernel
      have hl : raw7751step2Labels = raw7751step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7751step1 raw7751step1Labels permutation14 hz
    mixedMoment B raw7751step2 raw7751step2Labels = mixedMoment B raw7751step3 raw7751step3Labels := by
      have ha : raw7751step3 = (fun i j => raw7751step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7751step3 raw7751step2; decide +kernel
      have hl : raw7751step3Labels = raw7751step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7751step2 raw7751step2Labels permutation2 permutation3
    _ = mixedMoment B node1310 node1310Labels := by rfl

def raw7752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7752step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7752step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw7752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7752 raw7752Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw7752 raw7752Labels = mixedMoment B raw7752step0 raw7752step0Labels := by
      have hz : ∀ j, raw7752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7752step0 = (fun i j => raw7752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7752step0 raw7752; decide +kernel
      have hl : raw7752step0Labels = raw7752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7752 raw7752Labels permutation434 hz
    mixedMoment B raw7752step0 raw7752step0Labels = mixedMoment B raw7752step1 raw7752step1Labels := by
      have hz : ∀ j, raw7752step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7752step1 = (fun i j => raw7752step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7752step1 raw7752step0; decide +kernel
      have hl : raw7752step1Labels = raw7752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7752step0 raw7752step0Labels permutation80 hz
    mixedMoment B raw7752step1 raw7752step1Labels = mixedMoment B raw7752step2 raw7752step2Labels := by
      have ha : raw7752step2 = (fun i j => raw7752step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7752step2 raw7752step1; decide +kernel
      have hl : raw7752step2Labels = raw7752step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7752step1 raw7752step1Labels permutation8 permutation3
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw7753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7753step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7753step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw7753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7753 raw7753Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw7753 raw7753Labels = mixedMoment B raw7753step0 raw7753step0Labels := by
      have hz : ∀ j, raw7753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7753step0 = (fun i j => raw7753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7753step0 raw7753; decide +kernel
      have hl : raw7753step0Labels = raw7753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7753 raw7753Labels permutation434 hz
    mixedMoment B raw7753step0 raw7753step0Labels = mixedMoment B raw7753step1 raw7753step1Labels := by
      have hz : ∀ j, raw7753step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7753step1 = (fun i j => raw7753step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7753step1 raw7753step0; decide +kernel
      have hl : raw7753step1Labels = raw7753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7753step0 raw7753step0Labels permutation56 hz
    mixedMoment B raw7753step1 raw7753step1Labels = mixedMoment B raw7753step2 raw7753step2Labels := by
      have ha : raw7753step2 = (fun i j => raw7753step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7753step2 raw7753step1; decide +kernel
      have hl : raw7753step2Labels = raw7753step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7753step1 raw7753step1Labels permutation8 permutation3
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw7754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7754step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw7754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7754 raw7754Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw7754 raw7754Labels = mixedMoment B raw7754step0 raw7754step0Labels := by
      have hz : ∀ j, raw7754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7754step0 = (fun i j => raw7754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7754step0 raw7754; decide +kernel
      have hl : raw7754step0Labels = raw7754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7754 raw7754Labels permutation346 hz
    mixedMoment B raw7754step0 raw7754step0Labels = mixedMoment B raw7754step1 raw7754step1Labels := by
      have hz : ∀ j, raw7754step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7754step1 = (fun i j => raw7754step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7754step1 raw7754step0; decide +kernel
      have hl : raw7754step1Labels = raw7754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7754step0 raw7754step0Labels permutation56 hz
    mixedMoment B raw7754step1 raw7754step1Labels = mixedMoment B raw7754step2 raw7754step2Labels := by
      have ha : raw7754step2 = (fun i j => raw7754step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7754step2 raw7754step1; decide +kernel
      have hl : raw7754step2Labels = raw7754step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7754step1 raw7754step1Labels permutation8 permutation3
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw7755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7755step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7755step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7755step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 1, -3], ![1, -2, 1]]
def raw7755step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7755step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw7755step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7755 raw7755Labels = mixedMoment B node3125 node3125Labels := by
  calc
    mixedMoment B raw7755 raw7755Labels = mixedMoment B raw7755step0 raw7755step0Labels := by
      have hz : ∀ j, raw7755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7755step0 = (fun i j => raw7755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7755step0 raw7755; decide +kernel
      have hl : raw7755step0Labels = raw7755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7755 raw7755Labels permutation434 hz
    mixedMoment B raw7755step0 raw7755step0Labels = mixedMoment B raw7755step1 raw7755step1Labels := by
      have hz : ∀ j, raw7755step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7755step1 = (fun i j => raw7755step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7755step1 raw7755step0; decide +kernel
      have hl : raw7755step1Labels = raw7755step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7755step0 raw7755step0Labels permutation80 hz
    mixedMoment B raw7755step1 raw7755step1Labels = mixedMoment B raw7755step2 raw7755step2Labels := by
      have hz : ∀ j, raw7755step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7755step2 = (fun i j => raw7755step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7755step2 raw7755step1; decide +kernel
      have hl : raw7755step2Labels = raw7755step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7755step1 raw7755step1Labels permutation14 hz
    mixedMoment B raw7755step2 raw7755step2Labels = mixedMoment B raw7755step3 raw7755step3Labels := by
      have ha : raw7755step3 = (fun i j => raw7755step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7755step3 raw7755step2; decide +kernel
      have hl : raw7755step3Labels = raw7755step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7755step2 raw7755step2Labels permutation3 permutation3
    _ = mixedMoment B node3125 node3125Labels := by rfl

def raw7756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7756step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7756step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7756step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw7756step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7756step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![3, 1, -4]]
def raw7756step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7756 raw7756Labels = mixedMoment B node1289 node1289Labels := by
  calc
    mixedMoment B raw7756 raw7756Labels = mixedMoment B raw7756step0 raw7756step0Labels := by
      have hz : ∀ j, raw7756 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7756step0 = (fun i j => raw7756 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7756step0 raw7756; decide +kernel
      have hl : raw7756step0Labels = raw7756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7756 raw7756Labels permutation434 hz
    mixedMoment B raw7756step0 raw7756step0Labels = mixedMoment B raw7756step1 raw7756step1Labels := by
      have hz : ∀ j, raw7756step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7756step1 = (fun i j => raw7756step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7756step1 raw7756step0; decide +kernel
      have hl : raw7756step1Labels = raw7756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7756step0 raw7756step0Labels permutation80 hz
    mixedMoment B raw7756step1 raw7756step1Labels = mixedMoment B raw7756step2 raw7756step2Labels := by
      have hz : ∀ j, raw7756step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7756step2 = (fun i j => raw7756step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7756step2 raw7756step1; decide +kernel
      have hl : raw7756step2Labels = raw7756step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7756step1 raw7756step1Labels permutation14 hz
    mixedMoment B raw7756step2 raw7756step2Labels = mixedMoment B raw7756step3 raw7756step3Labels := by
      have ha : raw7756step3 = (fun i j => raw7756step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7756step3 raw7756step2; decide +kernel
      have hl : raw7756step3Labels = raw7756step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7756step2 raw7756step2Labels permutation2 permutation3
    _ = mixedMoment B node1289 node1289Labels := by rfl

def raw7757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7757step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw7757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7757step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw7757step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7757 raw7757Labels = mixedMoment B node1659 node1659Labels := by
  calc
    mixedMoment B raw7757 raw7757Labels = mixedMoment B raw7757step0 raw7757step0Labels := by
      have hz : ∀ j, raw7757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7757step0 = (fun i j => raw7757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7757step0 raw7757; decide +kernel
      have hl : raw7757step0Labels = raw7757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7757 raw7757Labels permutation434 hz
    mixedMoment B raw7757step0 raw7757step0Labels = mixedMoment B raw7757step1 raw7757step1Labels := by
      have hz : ∀ j, raw7757step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7757step1 = (fun i j => raw7757step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7757step1 raw7757step0; decide +kernel
      have hl : raw7757step1Labels = raw7757step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7757step0 raw7757step0Labels permutation80 hz
    mixedMoment B raw7757step1 raw7757step1Labels = mixedMoment B raw7757step2 raw7757step2Labels := by
      have ha : raw7757step2 = (fun i j => raw7757step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7757step2 raw7757step1; decide +kernel
      have hl : raw7757step2Labels = raw7757step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7757step1 raw7757step1Labels permutation31 permutation3
    mixedMoment B raw7757step2 raw7757step2Labels = mixedMoment B raw7757step3 raw7757step3Labels := by
      have ha : raw7757step3 = -raw7757step2 := by apply Matrix.ext; change ∀ i j, raw7757step3 i j = -(raw7757step2 i j); unfold raw7757step3 raw7757step2; decide +kernel
      have hl : raw7757step3Labels = raw7757step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1659 node1659Labels := by rfl

def raw7758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7758step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7758step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw7758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7758step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw7758step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7758 raw7758Labels = mixedMoment B node1659 node1659Labels := by
  calc
    mixedMoment B raw7758 raw7758Labels = mixedMoment B raw7758step0 raw7758step0Labels := by
      have hz : ∀ j, raw7758 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7758step0 = (fun i j => raw7758 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7758step0 raw7758; decide +kernel
      have hl : raw7758step0Labels = raw7758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7758 raw7758Labels permutation434 hz
    mixedMoment B raw7758step0 raw7758step0Labels = mixedMoment B raw7758step1 raw7758step1Labels := by
      have hz : ∀ j, raw7758step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7758step1 = (fun i j => raw7758step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7758step1 raw7758step0; decide +kernel
      have hl : raw7758step1Labels = raw7758step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7758step0 raw7758step0Labels permutation56 hz
    mixedMoment B raw7758step1 raw7758step1Labels = mixedMoment B raw7758step2 raw7758step2Labels := by
      have ha : raw7758step2 = (fun i j => raw7758step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7758step2 raw7758step1; decide +kernel
      have hl : raw7758step2Labels = raw7758step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7758step1 raw7758step1Labels permutation31 permutation3
    mixedMoment B raw7758step2 raw7758step2Labels = mixedMoment B raw7758step3 raw7758step3Labels := by
      have ha : raw7758step3 = -raw7758step2 := by apply Matrix.ext; change ∀ i j, raw7758step3 i j = -(raw7758step2 i j); unfold raw7758step3 raw7758step2; decide +kernel
      have hl : raw7758step3Labels = raw7758step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1659 node1659Labels := by rfl

def raw7759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7759step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7759step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw7759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7759step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw7759step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7759 raw7759Labels = mixedMoment B node1659 node1659Labels := by
  calc
    mixedMoment B raw7759 raw7759Labels = mixedMoment B raw7759step0 raw7759step0Labels := by
      have hz : ∀ j, raw7759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7759step0 = (fun i j => raw7759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7759step0 raw7759; decide +kernel
      have hl : raw7759step0Labels = raw7759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7759 raw7759Labels permutation346 hz
    mixedMoment B raw7759step0 raw7759step0Labels = mixedMoment B raw7759step1 raw7759step1Labels := by
      have hz : ∀ j, raw7759step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7759step1 = (fun i j => raw7759step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7759step1 raw7759step0; decide +kernel
      have hl : raw7759step1Labels = raw7759step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7759step0 raw7759step0Labels permutation56 hz
    mixedMoment B raw7759step1 raw7759step1Labels = mixedMoment B raw7759step2 raw7759step2Labels := by
      have ha : raw7759step2 = (fun i j => raw7759step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7759step2 raw7759step1; decide +kernel
      have hl : raw7759step2Labels = raw7759step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7759step1 raw7759step1Labels permutation31 permutation3
    mixedMoment B raw7759step2 raw7759step2Labels = mixedMoment B raw7759step3 raw7759step3Labels := by
      have ha : raw7759step3 = -raw7759step2 := by apply Matrix.ext; change ∀ i j, raw7759step3 i j = -(raw7759step2 i j); unfold raw7759step3 raw7759step2; decide +kernel
      have hl : raw7759step3Labels = raw7759step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1659 node1659Labels := by rfl

def raw7760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7760step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7760step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 3, -3], ![3, -4, 1]]
def raw7760step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7760step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw7760step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7760step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw7760step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7760 raw7760Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw7760 raw7760Labels = mixedMoment B raw7760step0 raw7760step0Labels := by
      have hz : ∀ j, raw7760 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7760step0 = (fun i j => raw7760 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7760step0 raw7760; decide +kernel
      have hl : raw7760step0Labels = raw7760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7760 raw7760Labels permutation434 hz
    mixedMoment B raw7760step0 raw7760step0Labels = mixedMoment B raw7760step1 raw7760step1Labels := by
      have hz : ∀ j, raw7760step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7760step1 = (fun i j => raw7760step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7760step1 raw7760step0; decide +kernel
      have hl : raw7760step1Labels = raw7760step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7760step0 raw7760step0Labels permutation80 hz
    mixedMoment B raw7760step1 raw7760step1Labels = mixedMoment B raw7760step2 raw7760step2Labels := by
      have hz : ∀ j, raw7760step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7760step2 = (fun i j => raw7760step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7760step2 raw7760step1; decide +kernel
      have hl : raw7760step2Labels = raw7760step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7760step1 raw7760step1Labels permutation14 hz
    mixedMoment B raw7760step2 raw7760step2Labels = mixedMoment B raw7760step3 raw7760step3Labels := by
      have ha : raw7760step3 = (fun i j => raw7760step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7760step3 raw7760step2; decide +kernel
      have hl : raw7760step3Labels = raw7760step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7760step2 raw7760step2Labels permutation7 permutation3
    mixedMoment B raw7760step3 raw7760step3Labels = mixedMoment B raw7760step4 raw7760step4Labels := by
      have ha : raw7760step4 = -raw7760step3 := by apply Matrix.ext; change ∀ i j, raw7760step4 i j = -(raw7760step3 i j); unfold raw7760step4 raw7760step3; decide +kernel
      have hl : raw7760step4Labels = raw7760step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1747 node1747Labels := by rfl

def raw7761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7761step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7761step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7761step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7761 raw7761Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw7761 raw7761Labels = mixedMoment B raw7761step0 raw7761step0Labels := by
      have hz : ∀ j, raw7761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7761step0 = (fun i j => raw7761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7761step0 raw7761; decide +kernel
      have hl : raw7761step0Labels = raw7761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7761 raw7761Labels permutation434 hz
    mixedMoment B raw7761step0 raw7761step0Labels = mixedMoment B raw7761step1 raw7761step1Labels := by
      have hz : ∀ j, raw7761step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7761step1 = (fun i j => raw7761step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7761step1 raw7761step0; decide +kernel
      have hl : raw7761step1Labels = raw7761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7761step0 raw7761step0Labels permutation80 hz
    mixedMoment B raw7761step1 raw7761step1Labels = mixedMoment B raw7761step2 raw7761step2Labels := by
      have ha : raw7761step2 = (fun i j => raw7761step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7761step2 raw7761step1; decide +kernel
      have hl : raw7761step2Labels = raw7761step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7761step1 raw7761step1Labels permutation26 permutation5
    mixedMoment B raw7761step2 raw7761step2Labels = mixedMoment B raw7761step3 raw7761step3Labels := by
      have ha : raw7761step3 = raw7761step2 := by apply Matrix.ext; unfold raw7761step3 raw7761step2; decide +kernel
      have hl : raw7761step2Labels = labelEmbedding1 ∘ raw7761step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7761step2 raw7761step2Labels raw7761step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw7762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7762step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7762step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7762step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7762step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7762 raw7762Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw7762 raw7762Labels = mixedMoment B raw7762step0 raw7762step0Labels := by
      have hz : ∀ j, raw7762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7762step0 = (fun i j => raw7762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7762step0 raw7762; decide +kernel
      have hl : raw7762step0Labels = raw7762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7762 raw7762Labels permutation434 hz
    mixedMoment B raw7762step0 raw7762step0Labels = mixedMoment B raw7762step1 raw7762step1Labels := by
      have hz : ∀ j, raw7762step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7762step1 = (fun i j => raw7762step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7762step1 raw7762step0; decide +kernel
      have hl : raw7762step1Labels = raw7762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7762step0 raw7762step0Labels permutation56 hz
    mixedMoment B raw7762step1 raw7762step1Labels = mixedMoment B raw7762step2 raw7762step2Labels := by
      have ha : raw7762step2 = (fun i j => raw7762step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7762step2 raw7762step1; decide +kernel
      have hl : raw7762step2Labels = raw7762step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7762step1 raw7762step1Labels permutation26 permutation5
    mixedMoment B raw7762step2 raw7762step2Labels = mixedMoment B raw7762step3 raw7762step3Labels := by
      have ha : raw7762step3 = raw7762step2 := by apply Matrix.ext; unfold raw7762step3 raw7762step2; decide +kernel
      have hl : raw7762step2Labels = labelEmbedding1 ∘ raw7762step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7762step2 raw7762step2Labels raw7762step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw7763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7763step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7763 raw7763Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw7763 raw7763Labels = mixedMoment B raw7763step0 raw7763step0Labels := by
      have hz : ∀ j, raw7763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7763step0 = (fun i j => raw7763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7763step0 raw7763; decide +kernel
      have hl : raw7763step0Labels = raw7763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7763 raw7763Labels permutation346 hz
    mixedMoment B raw7763step0 raw7763step0Labels = mixedMoment B raw7763step1 raw7763step1Labels := by
      have hz : ∀ j, raw7763step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7763step1 = (fun i j => raw7763step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7763step1 raw7763step0; decide +kernel
      have hl : raw7763step1Labels = raw7763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7763step0 raw7763step0Labels permutation56 hz
    mixedMoment B raw7763step1 raw7763step1Labels = mixedMoment B raw7763step2 raw7763step2Labels := by
      have ha : raw7763step2 = (fun i j => raw7763step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7763step2 raw7763step1; decide +kernel
      have hl : raw7763step2Labels = raw7763step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7763step1 raw7763step1Labels permutation26 permutation5
    mixedMoment B raw7763step2 raw7763step2Labels = mixedMoment B raw7763step3 raw7763step3Labels := by
      have ha : raw7763step3 = raw7763step2 := by apply Matrix.ext; unfold raw7763step3 raw7763step2; decide +kernel
      have hl : raw7763step2Labels = labelEmbedding1 ∘ raw7763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7763step2 raw7763step2Labels raw7763step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw7764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7764step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7764step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7764step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]
def raw7764step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7764step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw7764step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7764step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw7764step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7764 raw7764Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw7764 raw7764Labels = mixedMoment B raw7764step0 raw7764step0Labels := by
      have hz : ∀ j, raw7764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7764step0 = (fun i j => raw7764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7764step0 raw7764; decide +kernel
      have hl : raw7764step0Labels = raw7764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7764 raw7764Labels permutation434 hz
    mixedMoment B raw7764step0 raw7764step0Labels = mixedMoment B raw7764step1 raw7764step1Labels := by
      have hz : ∀ j, raw7764step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7764step1 = (fun i j => raw7764step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7764step1 raw7764step0; decide +kernel
      have hl : raw7764step1Labels = raw7764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7764step0 raw7764step0Labels permutation80 hz
    mixedMoment B raw7764step1 raw7764step1Labels = mixedMoment B raw7764step2 raw7764step2Labels := by
      have hz : ∀ j, raw7764step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7764step2 = (fun i j => raw7764step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7764step2 raw7764step1; decide +kernel
      have hl : raw7764step2Labels = raw7764step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7764step1 raw7764step1Labels permutation14 hz
    mixedMoment B raw7764step2 raw7764step2Labels = mixedMoment B raw7764step3 raw7764step3Labels := by
      have ha : raw7764step3 = (fun i j => raw7764step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7764step3 raw7764step2; decide +kernel
      have hl : raw7764step3Labels = raw7764step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7764step2 raw7764step2Labels permutation6 permutation5
    mixedMoment B raw7764step3 raw7764step3Labels = mixedMoment B raw7764step4 raw7764step4Labels := by
      have ha : raw7764step4 = raw7764step3 := by apply Matrix.ext; unfold raw7764step4 raw7764step3; decide +kernel
      have hl : raw7764step3Labels = labelEmbedding1 ∘ raw7764step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7764step3 raw7764step3Labels raw7764step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

def raw7765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7765step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7765step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7765step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![1, -2, 1]]
def raw7765step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7765step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw7765step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7765step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw7765step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7765 raw7765Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw7765 raw7765Labels = mixedMoment B raw7765step0 raw7765step0Labels := by
      have hz : ∀ j, raw7765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7765step0 = (fun i j => raw7765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7765step0 raw7765; decide +kernel
      have hl : raw7765step0Labels = raw7765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7765 raw7765Labels permutation434 hz
    mixedMoment B raw7765step0 raw7765step0Labels = mixedMoment B raw7765step1 raw7765step1Labels := by
      have hz : ∀ j, raw7765step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7765step1 = (fun i j => raw7765step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7765step1 raw7765step0; decide +kernel
      have hl : raw7765step1Labels = raw7765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7765step0 raw7765step0Labels permutation80 hz
    mixedMoment B raw7765step1 raw7765step1Labels = mixedMoment B raw7765step2 raw7765step2Labels := by
      have hz : ∀ j, raw7765step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7765step2 = (fun i j => raw7765step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7765step2 raw7765step1; decide +kernel
      have hl : raw7765step2Labels = raw7765step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7765step1 raw7765step1Labels permutation14 hz
    mixedMoment B raw7765step2 raw7765step2Labels = mixedMoment B raw7765step3 raw7765step3Labels := by
      have ha : raw7765step3 = (fun i j => raw7765step2 (permutation5 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7765step3 raw7765step2; decide +kernel
      have hl : raw7765step3Labels = raw7765step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7765step2 raw7765step2Labels permutation5 permutation7
    mixedMoment B raw7765step3 raw7765step3Labels = mixedMoment B raw7765step4 raw7765step4Labels := by
      have ha : raw7765step4 = raw7765step3 := by apply Matrix.ext; unfold raw7765step4 raw7765step3; decide +kernel
      have hl : raw7765step3Labels = labelEmbedding1 ∘ raw7765step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7765step3 raw7765step3Labels raw7765step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3121 node3121Labels := by rfl

def raw7766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7766step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7766step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7766step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7766step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7766step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7766 raw7766Labels = mixedMoment B node2521 node2521Labels := by
  calc
    mixedMoment B raw7766 raw7766Labels = mixedMoment B raw7766step0 raw7766step0Labels := by
      have hz : ∀ j, raw7766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7766step0 = (fun i j => raw7766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7766step0 raw7766; decide +kernel
      have hl : raw7766step0Labels = raw7766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7766 raw7766Labels permutation434 hz
    mixedMoment B raw7766step0 raw7766step0Labels = mixedMoment B raw7766step1 raw7766step1Labels := by
      have hz : ∀ j, raw7766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7766step1 = (fun i j => raw7766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7766step1 raw7766step0; decide +kernel
      have hl : raw7766step1Labels = raw7766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7766step0 raw7766step0Labels permutation80 hz
    mixedMoment B raw7766step1 raw7766step1Labels = mixedMoment B raw7766step2 raw7766step2Labels := by
      have ha : raw7766step2 = (fun i j => raw7766step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7766step2 raw7766step1; decide +kernel
      have hl : raw7766step2Labels = raw7766step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7766step1 raw7766step1Labels permutation29 permutation5
    mixedMoment B raw7766step2 raw7766step2Labels = mixedMoment B raw7766step3 raw7766step3Labels := by
      have ha : raw7766step3 = raw7766step2 := by apply Matrix.ext; unfold raw7766step3 raw7766step2; decide +kernel
      have hl : raw7766step2Labels = labelEmbedding1 ∘ raw7766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7766step2 raw7766step2Labels raw7766step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2521 node2521Labels := by rfl

def raw7767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7767step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7767step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7767step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7767 raw7767Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7767 raw7767Labels = mixedMoment B raw7767step0 raw7767step0Labels := by
      have hz : ∀ j, raw7767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7767step0 = (fun i j => raw7767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7767step0 raw7767; decide +kernel
      have hl : raw7767step0Labels = raw7767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7767 raw7767Labels permutation434 hz
    mixedMoment B raw7767step0 raw7767step0Labels = mixedMoment B raw7767step1 raw7767step1Labels := by
      have ha : raw7767step1 = (fun i j => raw7767step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7767step1 raw7767step0; decide +kernel
      have hl : raw7767step1Labels = raw7767step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7767step0 raw7767step0Labels permutation136 permutation5
    mixedMoment B raw7767step1 raw7767step1Labels = mixedMoment B raw7767step2 raw7767step2Labels := by
      have ha : raw7767step2 = raw7767step1 := by apply Matrix.ext; unfold raw7767step2 raw7767step1; decide +kernel
      have hl : raw7767step1Labels = labelEmbedding1 ∘ raw7767step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7767step1 raw7767step1Labels raw7767step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

def raw7768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7768step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7768 raw7768Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7768 raw7768Labels = mixedMoment B raw7768step0 raw7768step0Labels := by
      have hz : ∀ j, raw7768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7768step0 = (fun i j => raw7768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7768step0 raw7768; decide +kernel
      have hl : raw7768step0Labels = raw7768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7768 raw7768Labels permutation346 hz
    mixedMoment B raw7768step0 raw7768step0Labels = mixedMoment B raw7768step1 raw7768step1Labels := by
      have ha : raw7768step1 = (fun i j => raw7768step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7768step1 raw7768step0; decide +kernel
      have hl : raw7768step1Labels = raw7768step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7768step0 raw7768step0Labels permutation136 permutation5
    mixedMoment B raw7768step1 raw7768step1Labels = mixedMoment B raw7768step2 raw7768step2Labels := by
      have ha : raw7768step2 = raw7768step1 := by apply Matrix.ext; unfold raw7768step2 raw7768step1; decide +kernel
      have hl : raw7768step1Labels = labelEmbedding1 ∘ raw7768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7768step1 raw7768step1Labels raw7768step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

def raw7769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7769step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7769step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7769step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7769step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7769step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7769 raw7769Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw7769 raw7769Labels = mixedMoment B raw7769step0 raw7769step0Labels := by
      have hz : ∀ j, raw7769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7769step0 = (fun i j => raw7769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7769step0 raw7769; decide +kernel
      have hl : raw7769step0Labels = raw7769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7769 raw7769Labels permutation434 hz
    mixedMoment B raw7769step0 raw7769step0Labels = mixedMoment B raw7769step1 raw7769step1Labels := by
      have hz : ∀ j, raw7769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7769step1 = (fun i j => raw7769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7769step1 raw7769step0; decide +kernel
      have hl : raw7769step1Labels = raw7769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7769step0 raw7769step0Labels permutation80 hz
    mixedMoment B raw7769step1 raw7769step1Labels = mixedMoment B raw7769step2 raw7769step2Labels := by
      have ha : raw7769step2 = (fun i j => raw7769step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7769step2 raw7769step1; decide +kernel
      have hl : raw7769step2Labels = raw7769step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7769step1 raw7769step1Labels permutation28 permutation5
    mixedMoment B raw7769step2 raw7769step2Labels = mixedMoment B raw7769step3 raw7769step3Labels := by
      have ha : raw7769step3 = raw7769step2 := by apply Matrix.ext; unfold raw7769step3 raw7769step2; decide +kernel
      have hl : raw7769step2Labels = labelEmbedding1 ∘ raw7769step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7769step2 raw7769step2Labels raw7769step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw7770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7770step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7770step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7770step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7770step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7770step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7770step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7770 raw7770Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw7770 raw7770Labels = mixedMoment B raw7770step0 raw7770step0Labels := by
      have hz : ∀ j, raw7770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7770step0 = (fun i j => raw7770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7770step0 raw7770; decide +kernel
      have hl : raw7770step0Labels = raw7770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7770 raw7770Labels permutation434 hz
    mixedMoment B raw7770step0 raw7770step0Labels = mixedMoment B raw7770step1 raw7770step1Labels := by
      have hz : ∀ j, raw7770step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7770step1 = (fun i j => raw7770step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7770step1 raw7770step0; decide +kernel
      have hl : raw7770step1Labels = raw7770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7770step0 raw7770step0Labels permutation80 hz
    mixedMoment B raw7770step1 raw7770step1Labels = mixedMoment B raw7770step2 raw7770step2Labels := by
      have ha : raw7770step2 = (fun i j => raw7770step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7770step2 raw7770step1; decide +kernel
      have hl : raw7770step2Labels = raw7770step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7770step1 raw7770step1Labels permutation23 permutation7
    mixedMoment B raw7770step2 raw7770step2Labels = mixedMoment B raw7770step3 raw7770step3Labels := by
      have ha : raw7770step3 = raw7770step2 := by apply Matrix.ext; unfold raw7770step3 raw7770step2; decide +kernel
      have hl : raw7770step2Labels = labelEmbedding1 ∘ raw7770step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7770step2 raw7770step2Labels raw7770step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw7771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7771step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7771step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7771step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7771step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7771 raw7771Labels = mixedMoment B node2521 node2521Labels := by
  calc
    mixedMoment B raw7771 raw7771Labels = mixedMoment B raw7771step0 raw7771step0Labels := by
      have hz : ∀ j, raw7771 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7771step0 = (fun i j => raw7771 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7771step0 raw7771; decide +kernel
      have hl : raw7771step0Labels = raw7771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7771 raw7771Labels permutation434 hz
    mixedMoment B raw7771step0 raw7771step0Labels = mixedMoment B raw7771step1 raw7771step1Labels := by
      have hz : ∀ j, raw7771step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7771step1 = (fun i j => raw7771step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7771step1 raw7771step0; decide +kernel
      have hl : raw7771step1Labels = raw7771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7771step0 raw7771step0Labels permutation56 hz
    mixedMoment B raw7771step1 raw7771step1Labels = mixedMoment B raw7771step2 raw7771step2Labels := by
      have ha : raw7771step2 = (fun i j => raw7771step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7771step2 raw7771step1; decide +kernel
      have hl : raw7771step2Labels = raw7771step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7771step1 raw7771step1Labels permutation29 permutation5
    mixedMoment B raw7771step2 raw7771step2Labels = mixedMoment B raw7771step3 raw7771step3Labels := by
      have ha : raw7771step3 = raw7771step2 := by apply Matrix.ext; unfold raw7771step3 raw7771step2; decide +kernel
      have hl : raw7771step2Labels = labelEmbedding1 ∘ raw7771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7771step2 raw7771step2Labels raw7771step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2521 node2521Labels := by rfl

def raw7772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7772step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7772 raw7772Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7772 raw7772Labels = mixedMoment B raw7772step0 raw7772step0Labels := by
      have hz : ∀ j, raw7772 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7772step0 = (fun i j => raw7772 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7772step0 raw7772; decide +kernel
      have hl : raw7772step0Labels = raw7772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7772 raw7772Labels permutation434 hz
    mixedMoment B raw7772step0 raw7772step0Labels = mixedMoment B raw7772step1 raw7772step1Labels := by
      have ha : raw7772step1 = (fun i j => raw7772step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7772step1 raw7772step0; decide +kernel
      have hl : raw7772step1Labels = raw7772step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7772step0 raw7772step0Labels permutation142 permutation5
    mixedMoment B raw7772step1 raw7772step1Labels = mixedMoment B raw7772step2 raw7772step2Labels := by
      have ha : raw7772step2 = raw7772step1 := by apply Matrix.ext; unfold raw7772step2 raw7772step1; decide +kernel
      have hl : raw7772step1Labels = labelEmbedding1 ∘ raw7772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7772step1 raw7772step1Labels raw7772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

def raw7773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7773step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7773step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7773 raw7773Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7773 raw7773Labels = mixedMoment B raw7773step0 raw7773step0Labels := by
      have hz : ∀ j, raw7773 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7773step0 = (fun i j => raw7773 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7773step0 raw7773; decide +kernel
      have hl : raw7773step0Labels = raw7773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7773 raw7773Labels permutation265 hz
    mixedMoment B raw7773step0 raw7773step0Labels = mixedMoment B raw7773step1 raw7773step1Labels := by
      have ha : raw7773step1 = (fun i j => raw7773step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7773step1 raw7773step0; decide +kernel
      have hl : raw7773step1Labels = raw7773step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7773step0 raw7773step0Labels permutation136 permutation5
    mixedMoment B raw7773step1 raw7773step1Labels = mixedMoment B raw7773step2 raw7773step2Labels := by
      have ha : raw7773step2 = raw7773step1 := by apply Matrix.ext; unfold raw7773step2 raw7773step1; decide +kernel
      have hl : raw7773step1Labels = labelEmbedding1 ∘ raw7773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7773step1 raw7773step1Labels raw7773step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

def raw7774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7774step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7774step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7774step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7774step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7774step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7774 raw7774Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw7774 raw7774Labels = mixedMoment B raw7774step0 raw7774step0Labels := by
      have hz : ∀ j, raw7774 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7774step0 = (fun i j => raw7774 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7774step0 raw7774; decide +kernel
      have hl : raw7774step0Labels = raw7774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7774 raw7774Labels permutation434 hz
    mixedMoment B raw7774step0 raw7774step0Labels = mixedMoment B raw7774step1 raw7774step1Labels := by
      have hz : ∀ j, raw7774step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7774step1 = (fun i j => raw7774step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7774step1 raw7774step0; decide +kernel
      have hl : raw7774step1Labels = raw7774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7774step0 raw7774step0Labels permutation56 hz
    mixedMoment B raw7774step1 raw7774step1Labels = mixedMoment B raw7774step2 raw7774step2Labels := by
      have ha : raw7774step2 = (fun i j => raw7774step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7774step2 raw7774step1; decide +kernel
      have hl : raw7774step2Labels = raw7774step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7774step1 raw7774step1Labels permutation28 permutation5
    mixedMoment B raw7774step2 raw7774step2Labels = mixedMoment B raw7774step3 raw7774step3Labels := by
      have ha : raw7774step3 = raw7774step2 := by apply Matrix.ext; unfold raw7774step3 raw7774step2; decide +kernel
      have hl : raw7774step2Labels = labelEmbedding1 ∘ raw7774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7774step2 raw7774step2Labels raw7774step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw7775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7775step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7775step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7775step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7775step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7775 raw7775Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw7775 raw7775Labels = mixedMoment B raw7775step0 raw7775step0Labels := by
      have hz : ∀ j, raw7775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7775step0 = (fun i j => raw7775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7775step0 raw7775; decide +kernel
      have hl : raw7775step0Labels = raw7775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7775 raw7775Labels permutation434 hz
    mixedMoment B raw7775step0 raw7775step0Labels = mixedMoment B raw7775step1 raw7775step1Labels := by
      have hz : ∀ j, raw7775step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7775step1 = (fun i j => raw7775step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7775step1 raw7775step0; decide +kernel
      have hl : raw7775step1Labels = raw7775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7775step0 raw7775step0Labels permutation56 hz
    mixedMoment B raw7775step1 raw7775step1Labels = mixedMoment B raw7775step2 raw7775step2Labels := by
      have ha : raw7775step2 = (fun i j => raw7775step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7775step2 raw7775step1; decide +kernel
      have hl : raw7775step2Labels = raw7775step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7775step1 raw7775step1Labels permutation23 permutation7
    mixedMoment B raw7775step2 raw7775step2Labels = mixedMoment B raw7775step3 raw7775step3Labels := by
      have ha : raw7775step3 = raw7775step2 := by apply Matrix.ext; unfold raw7775step3 raw7775step2; decide +kernel
      have hl : raw7775step2Labels = labelEmbedding1 ∘ raw7775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7775step2 raw7775step2Labels raw7775step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw7776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7776step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7776step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7776step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7776step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7776step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7776 raw7776Labels = mixedMoment B node2521 node2521Labels := by
  calc
    mixedMoment B raw7776 raw7776Labels = mixedMoment B raw7776step0 raw7776step0Labels := by
      have hz : ∀ j, raw7776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7776step0 = (fun i j => raw7776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7776step0 raw7776; decide +kernel
      have hl : raw7776step0Labels = raw7776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7776 raw7776Labels permutation346 hz
    mixedMoment B raw7776step0 raw7776step0Labels = mixedMoment B raw7776step1 raw7776step1Labels := by
      have hz : ∀ j, raw7776step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7776step1 = (fun i j => raw7776step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7776step1 raw7776step0; decide +kernel
      have hl : raw7776step1Labels = raw7776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7776step0 raw7776step0Labels permutation56 hz
    mixedMoment B raw7776step1 raw7776step1Labels = mixedMoment B raw7776step2 raw7776step2Labels := by
      have ha : raw7776step2 = (fun i j => raw7776step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7776step2 raw7776step1; decide +kernel
      have hl : raw7776step2Labels = raw7776step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7776step1 raw7776step1Labels permutation29 permutation5
    mixedMoment B raw7776step2 raw7776step2Labels = mixedMoment B raw7776step3 raw7776step3Labels := by
      have ha : raw7776step3 = raw7776step2 := by apply Matrix.ext; unfold raw7776step3 raw7776step2; decide +kernel
      have hl : raw7776step2Labels = labelEmbedding1 ∘ raw7776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7776step2 raw7776step2Labels raw7776step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2521 node2521Labels := by rfl

def raw7777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7777step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7777step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7777 raw7777Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7777 raw7777Labels = mixedMoment B raw7777step0 raw7777step0Labels := by
      have hz : ∀ j, raw7777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7777step0 = (fun i j => raw7777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7777step0 raw7777; decide +kernel
      have hl : raw7777step0Labels = raw7777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7777 raw7777Labels permutation346 hz
    mixedMoment B raw7777step0 raw7777step0Labels = mixedMoment B raw7777step1 raw7777step1Labels := by
      have ha : raw7777step1 = (fun i j => raw7777step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7777step1 raw7777step0; decide +kernel
      have hl : raw7777step1Labels = raw7777step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7777step0 raw7777step0Labels permutation142 permutation5
    mixedMoment B raw7777step1 raw7777step1Labels = mixedMoment B raw7777step2 raw7777step2Labels := by
      have ha : raw7777step2 = raw7777step1 := by apply Matrix.ext; unfold raw7777step2 raw7777step1; decide +kernel
      have hl : raw7777step1Labels = labelEmbedding1 ∘ raw7777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7777step1 raw7777step1Labels raw7777step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

def raw7778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7778step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7778step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7778 raw7778Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw7778 raw7778Labels = mixedMoment B raw7778step0 raw7778step0Labels := by
      have hz : ∀ j, raw7778 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7778step0 = (fun i j => raw7778 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7778step0 raw7778; decide +kernel
      have hl : raw7778step0Labels = raw7778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7778 raw7778Labels permutation265 hz
    mixedMoment B raw7778step0 raw7778step0Labels = mixedMoment B raw7778step1 raw7778step1Labels := by
      have ha : raw7778step1 = (fun i j => raw7778step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7778step1 raw7778step0; decide +kernel
      have hl : raw7778step1Labels = raw7778step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7778step0 raw7778step0Labels permutation142 permutation5
    mixedMoment B raw7778step1 raw7778step1Labels = mixedMoment B raw7778step2 raw7778step2Labels := by
      have ha : raw7778step2 = raw7778step1 := by apply Matrix.ext; unfold raw7778step2 raw7778step1; decide +kernel
      have hl : raw7778step1Labels = labelEmbedding1 ∘ raw7778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7778step1 raw7778step1Labels raw7778step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

def raw7779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7779step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7779step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7779step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7779step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7779 raw7779Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw7779 raw7779Labels = mixedMoment B raw7779step0 raw7779step0Labels := by
      have hz : ∀ j, raw7779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7779step0 = (fun i j => raw7779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7779step0 raw7779; decide +kernel
      have hl : raw7779step0Labels = raw7779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7779 raw7779Labels permutation346 hz
    mixedMoment B raw7779step0 raw7779step0Labels = mixedMoment B raw7779step1 raw7779step1Labels := by
      have hz : ∀ j, raw7779step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7779step1 = (fun i j => raw7779step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7779step1 raw7779step0; decide +kernel
      have hl : raw7779step1Labels = raw7779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7779step0 raw7779step0Labels permutation56 hz
    mixedMoment B raw7779step1 raw7779step1Labels = mixedMoment B raw7779step2 raw7779step2Labels := by
      have ha : raw7779step2 = (fun i j => raw7779step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7779step2 raw7779step1; decide +kernel
      have hl : raw7779step2Labels = raw7779step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7779step1 raw7779step1Labels permutation28 permutation5
    mixedMoment B raw7779step2 raw7779step2Labels = mixedMoment B raw7779step3 raw7779step3Labels := by
      have ha : raw7779step3 = raw7779step2 := by apply Matrix.ext; unfold raw7779step3 raw7779step2; decide +kernel
      have hl : raw7779step2Labels = labelEmbedding1 ∘ raw7779step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7779step2 raw7779step2Labels raw7779step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw7780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7780step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7780step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7780step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7780step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7780 raw7780Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw7780 raw7780Labels = mixedMoment B raw7780step0 raw7780step0Labels := by
      have hz : ∀ j, raw7780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7780step0 = (fun i j => raw7780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7780step0 raw7780; decide +kernel
      have hl : raw7780step0Labels = raw7780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7780 raw7780Labels permutation346 hz
    mixedMoment B raw7780step0 raw7780step0Labels = mixedMoment B raw7780step1 raw7780step1Labels := by
      have hz : ∀ j, raw7780step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7780step1 = (fun i j => raw7780step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7780step1 raw7780step0; decide +kernel
      have hl : raw7780step1Labels = raw7780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7780step0 raw7780step0Labels permutation56 hz
    mixedMoment B raw7780step1 raw7780step1Labels = mixedMoment B raw7780step2 raw7780step2Labels := by
      have ha : raw7780step2 = (fun i j => raw7780step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7780step2 raw7780step1; decide +kernel
      have hl : raw7780step2Labels = raw7780step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7780step1 raw7780step1Labels permutation23 permutation7
    mixedMoment B raw7780step2 raw7780step2Labels = mixedMoment B raw7780step3 raw7780step3Labels := by
      have ha : raw7780step3 = raw7780step2 := by apply Matrix.ext; unfold raw7780step3 raw7780step2; decide +kernel
      have hl : raw7780step2Labels = labelEmbedding1 ∘ raw7780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7780step2 raw7780step2Labels raw7780step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw7781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7781step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7781step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7781step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 1, -3], ![2, -3, 1]]
def raw7781step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7781step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw7781step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7781step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw7781step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7781 raw7781Labels = mixedMoment B node2780 node2780Labels := by
  calc
    mixedMoment B raw7781 raw7781Labels = mixedMoment B raw7781step0 raw7781step0Labels := by
      have hz : ∀ j, raw7781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7781step0 = (fun i j => raw7781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7781step0 raw7781; decide +kernel
      have hl : raw7781step0Labels = raw7781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7781 raw7781Labels permutation434 hz
    mixedMoment B raw7781step0 raw7781step0Labels = mixedMoment B raw7781step1 raw7781step1Labels := by
      have hz : ∀ j, raw7781step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7781step1 = (fun i j => raw7781step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7781step1 raw7781step0; decide +kernel
      have hl : raw7781step1Labels = raw7781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7781step0 raw7781step0Labels permutation80 hz
    mixedMoment B raw7781step1 raw7781step1Labels = mixedMoment B raw7781step2 raw7781step2Labels := by
      have hz : ∀ j, raw7781step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7781step2 = (fun i j => raw7781step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7781step2 raw7781step1; decide +kernel
      have hl : raw7781step2Labels = raw7781step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7781step1 raw7781step1Labels permutation14 hz
    mixedMoment B raw7781step2 raw7781step2Labels = mixedMoment B raw7781step3 raw7781step3Labels := by
      have ha : raw7781step3 = (fun i j => raw7781step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7781step3 raw7781step2; decide +kernel
      have hl : raw7781step3Labels = raw7781step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7781step2 raw7781step2Labels permutation7 permutation5
    mixedMoment B raw7781step3 raw7781step3Labels = mixedMoment B raw7781step4 raw7781step4Labels := by
      have ha : raw7781step4 = raw7781step3 := by apply Matrix.ext; unfold raw7781step4 raw7781step3; decide +kernel
      have hl : raw7781step3Labels = labelEmbedding1 ∘ raw7781step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7781step3 raw7781step3Labels raw7781step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2780 node2780Labels := by rfl

def raw7782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7782step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7782step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7782step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7782step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7782 raw7782Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw7782 raw7782Labels = mixedMoment B raw7782step0 raw7782step0Labels := by
      have hz : ∀ j, raw7782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7782step0 = (fun i j => raw7782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7782step0 raw7782; decide +kernel
      have hl : raw7782step0Labels = raw7782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7782 raw7782Labels permutation434 hz
    mixedMoment B raw7782step0 raw7782step0Labels = mixedMoment B raw7782step1 raw7782step1Labels := by
      have hz : ∀ j, raw7782step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7782step1 = (fun i j => raw7782step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7782step1 raw7782step0; decide +kernel
      have hl : raw7782step1Labels = raw7782step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7782step0 raw7782step0Labels permutation80 hz
    mixedMoment B raw7782step1 raw7782step1Labels = mixedMoment B raw7782step2 raw7782step2Labels := by
      have ha : raw7782step2 = (fun i j => raw7782step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7782step2 raw7782step1; decide +kernel
      have hl : raw7782step2Labels = raw7782step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7782step1 raw7782step1Labels permutation23 permutation7
    mixedMoment B raw7782step2 raw7782step2Labels = mixedMoment B raw7782step3 raw7782step3Labels := by
      have ha : raw7782step3 = raw7782step2 := by apply Matrix.ext; unfold raw7782step3 raw7782step2; decide +kernel
      have hl : raw7782step2Labels = labelEmbedding1 ∘ raw7782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7782step2 raw7782step2Labels raw7782step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw7783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7783step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7783step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7783step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7783step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7783step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7783 raw7783Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw7783 raw7783Labels = mixedMoment B raw7783step0 raw7783step0Labels := by
      have hz : ∀ j, raw7783 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7783step0 = (fun i j => raw7783 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7783step0 raw7783; decide +kernel
      have hl : raw7783step0Labels = raw7783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7783 raw7783Labels permutation434 hz
    mixedMoment B raw7783step0 raw7783step0Labels = mixedMoment B raw7783step1 raw7783step1Labels := by
      have hz : ∀ j, raw7783step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7783step1 = (fun i j => raw7783step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7783step1 raw7783step0; decide +kernel
      have hl : raw7783step1Labels = raw7783step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7783step0 raw7783step0Labels permutation56 hz
    mixedMoment B raw7783step1 raw7783step1Labels = mixedMoment B raw7783step2 raw7783step2Labels := by
      have ha : raw7783step2 = (fun i j => raw7783step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7783step2 raw7783step1; decide +kernel
      have hl : raw7783step2Labels = raw7783step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7783step1 raw7783step1Labels permutation23 permutation7
    mixedMoment B raw7783step2 raw7783step2Labels = mixedMoment B raw7783step3 raw7783step3Labels := by
      have ha : raw7783step3 = raw7783step2 := by apply Matrix.ext; unfold raw7783step3 raw7783step2; decide +kernel
      have hl : raw7783step2Labels = labelEmbedding1 ∘ raw7783step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7783step2 raw7783step2Labels raw7783step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw7784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7784step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7784step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7784step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7784 raw7784Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw7784 raw7784Labels = mixedMoment B raw7784step0 raw7784step0Labels := by
      have hz : ∀ j, raw7784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7784step0 = (fun i j => raw7784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7784step0 raw7784; decide +kernel
      have hl : raw7784step0Labels = raw7784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7784 raw7784Labels permutation346 hz
    mixedMoment B raw7784step0 raw7784step0Labels = mixedMoment B raw7784step1 raw7784step1Labels := by
      have hz : ∀ j, raw7784step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7784step1 = (fun i j => raw7784step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7784step1 raw7784step0; decide +kernel
      have hl : raw7784step1Labels = raw7784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7784step0 raw7784step0Labels permutation56 hz
    mixedMoment B raw7784step1 raw7784step1Labels = mixedMoment B raw7784step2 raw7784step2Labels := by
      have ha : raw7784step2 = (fun i j => raw7784step1 (permutation23 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7784step2 raw7784step1; decide +kernel
      have hl : raw7784step2Labels = raw7784step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7784step1 raw7784step1Labels permutation23 permutation7
    mixedMoment B raw7784step2 raw7784step2Labels = mixedMoment B raw7784step3 raw7784step3Labels := by
      have ha : raw7784step3 = raw7784step2 := by apply Matrix.ext; unfold raw7784step3 raw7784step2; decide +kernel
      have hl : raw7784step2Labels = labelEmbedding1 ∘ raw7784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7784step2 raw7784step2Labels raw7784step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw7785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7785step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7785step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7785step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 1, -3], ![1, -2, 1]]
def raw7785step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7785step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7785step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7785step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7785step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7785 raw7785Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw7785 raw7785Labels = mixedMoment B raw7785step0 raw7785step0Labels := by
      have hz : ∀ j, raw7785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7785step0 = (fun i j => raw7785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7785step0 raw7785; decide +kernel
      have hl : raw7785step0Labels = raw7785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7785 raw7785Labels permutation434 hz
    mixedMoment B raw7785step0 raw7785step0Labels = mixedMoment B raw7785step1 raw7785step1Labels := by
      have hz : ∀ j, raw7785step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7785step1 = (fun i j => raw7785step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7785step1 raw7785step0; decide +kernel
      have hl : raw7785step1Labels = raw7785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7785step0 raw7785step0Labels permutation80 hz
    mixedMoment B raw7785step1 raw7785step1Labels = mixedMoment B raw7785step2 raw7785step2Labels := by
      have hz : ∀ j, raw7785step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7785step2 = (fun i j => raw7785step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7785step2 raw7785step1; decide +kernel
      have hl : raw7785step2Labels = raw7785step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7785step1 raw7785step1Labels permutation14 hz
    mixedMoment B raw7785step2 raw7785step2Labels = mixedMoment B raw7785step3 raw7785step3Labels := by
      have ha : raw7785step3 = (fun i j => raw7785step2 (permutation5 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7785step3 raw7785step2; decide +kernel
      have hl : raw7785step3Labels = raw7785step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7785step2 raw7785step2Labels permutation5 permutation7
    mixedMoment B raw7785step3 raw7785step3Labels = mixedMoment B raw7785step4 raw7785step4Labels := by
      have ha : raw7785step4 = raw7785step3 := by apply Matrix.ext; unfold raw7785step4 raw7785step3; decide +kernel
      have hl : raw7785step3Labels = labelEmbedding1 ∘ raw7785step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7785step3 raw7785step3Labels raw7785step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw7786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7786step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7786step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw7786step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7786step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw7786step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7786step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw7786step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7786 raw7786Labels = mixedMoment B node1093 node1093Labels := by
  calc
    mixedMoment B raw7786 raw7786Labels = mixedMoment B raw7786step0 raw7786step0Labels := by
      have hz : ∀ j, raw7786 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7786step0 = (fun i j => raw7786 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7786step0 raw7786; decide +kernel
      have hl : raw7786step0Labels = raw7786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7786 raw7786Labels permutation434 hz
    mixedMoment B raw7786step0 raw7786step0Labels = mixedMoment B raw7786step1 raw7786step1Labels := by
      have hz : ∀ j, raw7786step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7786step1 = (fun i j => raw7786step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7786step1 raw7786step0; decide +kernel
      have hl : raw7786step1Labels = raw7786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7786step0 raw7786step0Labels permutation80 hz
    mixedMoment B raw7786step1 raw7786step1Labels = mixedMoment B raw7786step2 raw7786step2Labels := by
      have hz : ∀ j, raw7786step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7786step2 = (fun i j => raw7786step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7786step2 raw7786step1; decide +kernel
      have hl : raw7786step2Labels = raw7786step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7786step1 raw7786step1Labels permutation14 hz
    mixedMoment B raw7786step2 raw7786step2Labels = mixedMoment B raw7786step3 raw7786step3Labels := by
      have ha : raw7786step3 = (fun i j => raw7786step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7786step3 raw7786step2; decide +kernel
      have hl : raw7786step3Labels = raw7786step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7786step2 raw7786step2Labels permutation7 permutation5
    mixedMoment B raw7786step3 raw7786step3Labels = mixedMoment B raw7786step4 raw7786step4Labels := by
      have ha : raw7786step4 = raw7786step3 := by apply Matrix.ext; unfold raw7786step4 raw7786step3; decide +kernel
      have hl : raw7786step3Labels = labelEmbedding1 ∘ raw7786step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7786step3 raw7786step3Labels raw7786step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1093 node1093Labels := by rfl

def raw7787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7787step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7787step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7787step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7787 raw7787Labels = mixedMoment B node1088 node1088Labels := by
  calc
    mixedMoment B raw7787 raw7787Labels = mixedMoment B raw7787step0 raw7787step0Labels := by
      have hz : ∀ j, raw7787 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7787step0 = (fun i j => raw7787 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7787step0 raw7787; decide +kernel
      have hl : raw7787step0Labels = raw7787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7787 raw7787Labels permutation434 hz
    mixedMoment B raw7787step0 raw7787step0Labels = mixedMoment B raw7787step1 raw7787step1Labels := by
      have hz : ∀ j, raw7787step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7787step1 = (fun i j => raw7787step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7787step1 raw7787step0; decide +kernel
      have hl : raw7787step1Labels = raw7787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7787step0 raw7787step0Labels permutation80 hz
    mixedMoment B raw7787step1 raw7787step1Labels = mixedMoment B raw7787step2 raw7787step2Labels := by
      have ha : raw7787step2 = (fun i j => raw7787step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7787step2 raw7787step1; decide +kernel
      have hl : raw7787step2Labels = raw7787step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7787step1 raw7787step1Labels permutation28 permutation5
    mixedMoment B raw7787step2 raw7787step2Labels = mixedMoment B raw7787step3 raw7787step3Labels := by
      have ha : raw7787step3 = raw7787step2 := by apply Matrix.ext; unfold raw7787step3 raw7787step2; decide +kernel
      have hl : raw7787step2Labels = labelEmbedding1 ∘ raw7787step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7787step2 raw7787step2Labels raw7787step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1088 node1088Labels := by rfl

def raw7788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7788step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7788step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7788step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7788 raw7788Labels = mixedMoment B node1088 node1088Labels := by
  calc
    mixedMoment B raw7788 raw7788Labels = mixedMoment B raw7788step0 raw7788step0Labels := by
      have hz : ∀ j, raw7788 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7788step0 = (fun i j => raw7788 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7788step0 raw7788; decide +kernel
      have hl : raw7788step0Labels = raw7788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7788 raw7788Labels permutation434 hz
    mixedMoment B raw7788step0 raw7788step0Labels = mixedMoment B raw7788step1 raw7788step1Labels := by
      have hz : ∀ j, raw7788step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7788step1 = (fun i j => raw7788step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7788step1 raw7788step0; decide +kernel
      have hl : raw7788step1Labels = raw7788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7788step0 raw7788step0Labels permutation56 hz
    mixedMoment B raw7788step1 raw7788step1Labels = mixedMoment B raw7788step2 raw7788step2Labels := by
      have ha : raw7788step2 = (fun i j => raw7788step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7788step2 raw7788step1; decide +kernel
      have hl : raw7788step2Labels = raw7788step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7788step1 raw7788step1Labels permutation28 permutation5
    mixedMoment B raw7788step2 raw7788step2Labels = mixedMoment B raw7788step3 raw7788step3Labels := by
      have ha : raw7788step3 = raw7788step2 := by apply Matrix.ext; unfold raw7788step3 raw7788step2; decide +kernel
      have hl : raw7788step2Labels = labelEmbedding1 ∘ raw7788step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7788step2 raw7788step2Labels raw7788step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1088 node1088Labels := by rfl

def raw7789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7789step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7789step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7789step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7789step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7789step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7789 raw7789Labels = mixedMoment B node1088 node1088Labels := by
  calc
    mixedMoment B raw7789 raw7789Labels = mixedMoment B raw7789step0 raw7789step0Labels := by
      have hz : ∀ j, raw7789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7789step0 = (fun i j => raw7789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7789step0 raw7789; decide +kernel
      have hl : raw7789step0Labels = raw7789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7789 raw7789Labels permutation346 hz
    mixedMoment B raw7789step0 raw7789step0Labels = mixedMoment B raw7789step1 raw7789step1Labels := by
      have hz : ∀ j, raw7789step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7789step1 = (fun i j => raw7789step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7789step1 raw7789step0; decide +kernel
      have hl : raw7789step1Labels = raw7789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7789step0 raw7789step0Labels permutation56 hz
    mixedMoment B raw7789step1 raw7789step1Labels = mixedMoment B raw7789step2 raw7789step2Labels := by
      have ha : raw7789step2 = (fun i j => raw7789step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7789step2 raw7789step1; decide +kernel
      have hl : raw7789step2Labels = raw7789step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7789step1 raw7789step1Labels permutation28 permutation5
    mixedMoment B raw7789step2 raw7789step2Labels = mixedMoment B raw7789step3 raw7789step3Labels := by
      have ha : raw7789step3 = raw7789step2 := by apply Matrix.ext; unfold raw7789step3 raw7789step2; decide +kernel
      have hl : raw7789step2Labels = labelEmbedding1 ∘ raw7789step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7789step2 raw7789step2Labels raw7789step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1088 node1088Labels := by rfl

def raw7790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7790step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7790step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 3, -3], ![3, -4, 1]]
def raw7790step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7790step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw7790step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7790step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw7790step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7790 raw7790Labels = mixedMoment B node1092 node1092Labels := by
  calc
    mixedMoment B raw7790 raw7790Labels = mixedMoment B raw7790step0 raw7790step0Labels := by
      have hz : ∀ j, raw7790 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7790step0 = (fun i j => raw7790 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7790step0 raw7790; decide +kernel
      have hl : raw7790step0Labels = raw7790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7790 raw7790Labels permutation434 hz
    mixedMoment B raw7790step0 raw7790step0Labels = mixedMoment B raw7790step1 raw7790step1Labels := by
      have hz : ∀ j, raw7790step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7790step1 = (fun i j => raw7790step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7790step1 raw7790step0; decide +kernel
      have hl : raw7790step1Labels = raw7790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7790step0 raw7790step0Labels permutation80 hz
    mixedMoment B raw7790step1 raw7790step1Labels = mixedMoment B raw7790step2 raw7790step2Labels := by
      have hz : ∀ j, raw7790step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7790step2 = (fun i j => raw7790step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7790step2 raw7790step1; decide +kernel
      have hl : raw7790step2Labels = raw7790step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7790step1 raw7790step1Labels permutation14 hz
    mixedMoment B raw7790step2 raw7790step2Labels = mixedMoment B raw7790step3 raw7790step3Labels := by
      have ha : raw7790step3 = (fun i j => raw7790step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7790step3 raw7790step2; decide +kernel
      have hl : raw7790step3Labels = raw7790step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7790step2 raw7790step2Labels permutation6 permutation5
    mixedMoment B raw7790step3 raw7790step3Labels = mixedMoment B raw7790step4 raw7790step4Labels := by
      have ha : raw7790step4 = raw7790step3 := by apply Matrix.ext; unfold raw7790step4 raw7790step3; decide +kernel
      have hl : raw7790step3Labels = labelEmbedding1 ∘ raw7790step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7790step3 raw7790step3Labels raw7790step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1092 node1092Labels := by rfl

def raw7791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7791step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw7791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7791 raw7791Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw7791 raw7791Labels = mixedMoment B raw7791step0 raw7791step0Labels := by
      have hz : ∀ j, raw7791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7791step0 = (fun i j => raw7791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7791step0 raw7791; decide +kernel
      have hl : raw7791step0Labels = raw7791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7791 raw7791Labels permutation434 hz
    mixedMoment B raw7791step0 raw7791step0Labels = mixedMoment B raw7791step1 raw7791step1Labels := by
      have hz : ∀ j, raw7791step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7791step1 = (fun i j => raw7791step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7791step1 raw7791step0; decide +kernel
      have hl : raw7791step1Labels = raw7791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7791step0 raw7791step0Labels permutation80 hz
    mixedMoment B raw7791step1 raw7791step1Labels = mixedMoment B raw7791step2 raw7791step2Labels := by
      have hz : ∀ j, raw7791step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7791step2 = (fun i j => raw7791step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7791step2 raw7791step1; decide +kernel
      have hl : raw7791step2Labels = raw7791step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7791step1 raw7791step1Labels permutation14 hz
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw7792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7792 raw7792Labels = mixedMoment B node1303 node1303Labels := by
  calc
    mixedMoment B raw7792 raw7792Labels = mixedMoment B raw7792step0 raw7792step0Labels := by
      have hz : ∀ j, raw7792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7792step0 = (fun i j => raw7792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7792step0 raw7792; decide +kernel
      have hl : raw7792step0Labels = raw7792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7792 raw7792Labels permutation434 hz
    mixedMoment B raw7792step0 raw7792step0Labels = mixedMoment B raw7792step1 raw7792step1Labels := by
      have hz : ∀ j, raw7792step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7792step1 = (fun i j => raw7792step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7792step1 raw7792step0; decide +kernel
      have hl : raw7792step1Labels = raw7792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7792step0 raw7792step0Labels permutation80 hz
    _ = mixedMoment B node1303 node1303Labels := by rfl

def raw7793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7793 raw7793Labels = mixedMoment B node1303 node1303Labels := by
  calc
    mixedMoment B raw7793 raw7793Labels = mixedMoment B raw7793step0 raw7793step0Labels := by
      have hz : ∀ j, raw7793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7793step0 = (fun i j => raw7793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7793step0 raw7793; decide +kernel
      have hl : raw7793step0Labels = raw7793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7793 raw7793Labels permutation434 hz
    mixedMoment B raw7793step0 raw7793step0Labels = mixedMoment B raw7793step1 raw7793step1Labels := by
      have hz : ∀ j, raw7793step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7793step1 = (fun i j => raw7793step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7793step1 raw7793step0; decide +kernel
      have hl : raw7793step1Labels = raw7793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7793step0 raw7793step0Labels permutation56 hz
    _ = mixedMoment B node1303 node1303Labels := by rfl

def raw7794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7794 raw7794Labels = mixedMoment B node1303 node1303Labels := by
  calc
    mixedMoment B raw7794 raw7794Labels = mixedMoment B raw7794step0 raw7794step0Labels := by
      have hz : ∀ j, raw7794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7794step0 = (fun i j => raw7794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7794step0 raw7794; decide +kernel
      have hl : raw7794step0Labels = raw7794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7794 raw7794Labels permutation346 hz
    mixedMoment B raw7794step0 raw7794step0Labels = mixedMoment B raw7794step1 raw7794step1Labels := by
      have hz : ∀ j, raw7794step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7794step1 = (fun i j => raw7794step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7794step1 raw7794step0; decide +kernel
      have hl : raw7794step1Labels = raw7794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7794step0 raw7794step0Labels permutation56 hz
    _ = mixedMoment B node1303 node1303Labels := by rfl

def raw7795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7795step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 1, -3], ![2, -3, 1]]
def raw7795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7795step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw7795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7795 raw7795Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw7795 raw7795Labels = mixedMoment B raw7795step0 raw7795step0Labels := by
      have hz : ∀ j, raw7795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7795step0 = (fun i j => raw7795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7795step0 raw7795; decide +kernel
      have hl : raw7795step0Labels = raw7795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7795 raw7795Labels permutation434 hz
    mixedMoment B raw7795step0 raw7795step0Labels = mixedMoment B raw7795step1 raw7795step1Labels := by
      have hz : ∀ j, raw7795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7795step1 = (fun i j => raw7795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7795step1 raw7795step0; decide +kernel
      have hl : raw7795step1Labels = raw7795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7795step0 raw7795step0Labels permutation80 hz
    mixedMoment B raw7795step1 raw7795step1Labels = mixedMoment B raw7795step2 raw7795step2Labels := by
      have hz : ∀ j, raw7795step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7795step2 = (fun i j => raw7795step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7795step2 raw7795step1; decide +kernel
      have hl : raw7795step2Labels = raw7795step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7795step1 raw7795step1Labels permutation14 hz
    mixedMoment B raw7795step2 raw7795step2Labels = mixedMoment B raw7795step3 raw7795step3Labels := by
      have ha : raw7795step3 = (fun i j => raw7795step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7795step3 raw7795step2; decide +kernel
      have hl : raw7795step3Labels = raw7795step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7795step2 raw7795step2Labels permutation3 permutation2
    _ = mixedMoment B node1310 node1310Labels := by rfl

def raw7796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7796step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw7796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7796 raw7796Labels = mixedMoment B node1309 node1309Labels := by
  calc
    mixedMoment B raw7796 raw7796Labels = mixedMoment B raw7796step0 raw7796step0Labels := by
      have hz : ∀ j, raw7796 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7796step0 = (fun i j => raw7796 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7796step0 raw7796; decide +kernel
      have hl : raw7796step0Labels = raw7796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7796 raw7796Labels permutation434 hz
    mixedMoment B raw7796step0 raw7796step0Labels = mixedMoment B raw7796step1 raw7796step1Labels := by
      have hz : ∀ j, raw7796step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7796step1 = (fun i j => raw7796step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7796step1 raw7796step0; decide +kernel
      have hl : raw7796step1Labels = raw7796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7796step0 raw7796step0Labels permutation80 hz
    mixedMoment B raw7796step1 raw7796step1Labels = mixedMoment B raw7796step2 raw7796step2Labels := by
      have hz : ∀ j, raw7796step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7796step2 = (fun i j => raw7796step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7796step2 raw7796step1; decide +kernel
      have hl : raw7796step2Labels = raw7796step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7796step1 raw7796step1Labels permutation14 hz
    _ = mixedMoment B node1309 node1309Labels := by rfl

def raw7797 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![3, -3], ![-1, 1]]
def raw7797Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7797step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![3, -3], ![-1, 1]]
def raw7797step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7797step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![3, -3], ![-1, 1]]
def raw7797step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7797step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![3, -3], ![-1, 1]]
def raw7797step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7797step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw7797step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7797step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw7797step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical7797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7797 raw7797Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw7797 raw7797Labels = mixedMoment B raw7797step0 raw7797step0Labels := by
      have hz : ∀ j, raw7797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7797step0 = (fun i j => raw7797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7797step0 raw7797; decide +kernel
      have hl : raw7797step0Labels = raw7797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7797 raw7797Labels permutation434 hz
    mixedMoment B raw7797step0 raw7797step0Labels = mixedMoment B raw7797step1 raw7797step1Labels := by
      have hz : ∀ j, raw7797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7797step1 = (fun i j => raw7797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7797step1 raw7797step0; decide +kernel
      have hl : raw7797step1Labels = raw7797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7797step0 raw7797step0Labels permutation80 hz
    mixedMoment B raw7797step1 raw7797step1Labels = mixedMoment B raw7797step2 raw7797step2Labels := by
      have hz : ∀ j, raw7797step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7797step2 = (fun i j => raw7797step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7797step2 raw7797step1; decide +kernel
      have hl : raw7797step2Labels = raw7797step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7797step1 raw7797step1Labels permutation14 hz
    mixedMoment B raw7797step2 raw7797step2Labels = mixedMoment B raw7797step3 raw7797step3Labels := by
      have ha : raw7797step3 = (fun i j => raw7797step2 (permutation5 i) (permutation0 j)) := by apply Matrix.ext; unfold raw7797step3 raw7797step2; decide +kernel
      have hl : raw7797step3Labels = raw7797step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7797step2 raw7797step2Labels permutation5 permutation0
    mixedMoment B raw7797step3 raw7797step3Labels = mixedMoment B raw7797step4 raw7797step4Labels := by
      have ha : raw7797step4 = -raw7797step3 := by apply Matrix.ext; change ∀ i j, raw7797step4 i j = -(raw7797step3 i j); unfold raw7797step4 raw7797step3; decide +kernel
      have hl : raw7797step4Labels = raw7797step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw7798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7798 raw7798Labels = mixedMoment B node2597 node2597Labels := by
  calc
    mixedMoment B raw7798 raw7798Labels = mixedMoment B raw7798step0 raw7798step0Labels := by
      have hz : ∀ j, raw7798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7798step0 = (fun i j => raw7798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7798step0 raw7798; decide +kernel
      have hl : raw7798step0Labels = raw7798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7798 raw7798Labels permutation434 hz
    mixedMoment B raw7798step0 raw7798step0Labels = mixedMoment B raw7798step1 raw7798step1Labels := by
      have ha : raw7798step1 = (fun i j => raw7798step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7798step1 raw7798step0; decide +kernel
      have hl : raw7798step1Labels = raw7798step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7798step0 raw7798step0Labels permutation38 permutation2
    _ = mixedMoment B node2597 node2597Labels := by rfl

def raw7799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7799step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7799 raw7799Labels = mixedMoment B node2597 node2597Labels := by
  calc
    mixedMoment B raw7799 raw7799Labels = mixedMoment B raw7799step0 raw7799step0Labels := by
      have hz : ∀ j, raw7799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7799step0 = (fun i j => raw7799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7799step0 raw7799; decide +kernel
      have hl : raw7799step0Labels = raw7799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7799 raw7799Labels permutation346 hz
    mixedMoment B raw7799step0 raw7799step0Labels = mixedMoment B raw7799step1 raw7799step1Labels := by
      have ha : raw7799step1 = (fun i j => raw7799step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7799step1 raw7799step0; decide +kernel
      have hl : raw7799step1Labels = raw7799step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7799step0 raw7799step0Labels permutation38 permutation2
    _ = mixedMoment B node2597 node2597Labels := by rfl

def raw7800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7800step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw7800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7800step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw7800step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7800 raw7800Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw7800 raw7800Labels = mixedMoment B raw7800step0 raw7800step0Labels := by
      have hz : ∀ j, raw7800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7800step0 = (fun i j => raw7800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7800step0 raw7800; decide +kernel
      have hl : raw7800step0Labels = raw7800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7800 raw7800Labels permutation434 hz
    mixedMoment B raw7800step0 raw7800step0Labels = mixedMoment B raw7800step1 raw7800step1Labels := by
      have hz : ∀ j, raw7800step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7800step1 = (fun i j => raw7800step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7800step1 raw7800step0; decide +kernel
      have hl : raw7800step1Labels = raw7800step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7800step0 raw7800step0Labels permutation80 hz
    mixedMoment B raw7800step1 raw7800step1Labels = mixedMoment B raw7800step2 raw7800step2Labels := by
      have ha : raw7800step2 = (fun i j => raw7800step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7800step2 raw7800step1; decide +kernel
      have hl : raw7800step2Labels = raw7800step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7800step1 raw7800step1Labels permutation20 permutation4
    mixedMoment B raw7800step2 raw7800step2Labels = mixedMoment B raw7800step3 raw7800step3Labels := by
      have ha : raw7800step3 = -raw7800step2 := by apply Matrix.ext; change ∀ i j, raw7800step3 i j = -(raw7800step2 i j); unfold raw7800step3 raw7800step2; decide +kernel
      have hl : raw7800step3Labels = raw7800step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2134 node2134Labels := by rfl

def raw7801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw7801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7801 raw7801Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw7801 raw7801Labels = mixedMoment B raw7801step0 raw7801step0Labels := by
      have hz : ∀ j, raw7801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7801step0 = (fun i j => raw7801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7801step0 raw7801; decide +kernel
      have hl : raw7801step0Labels = raw7801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7801 raw7801Labels permutation434 hz
    mixedMoment B raw7801step0 raw7801step0Labels = mixedMoment B raw7801step1 raw7801step1Labels := by
      have hz : ∀ j, raw7801step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7801step1 = (fun i j => raw7801step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7801step1 raw7801step0; decide +kernel
      have hl : raw7801step1Labels = raw7801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7801step0 raw7801step0Labels permutation80 hz
    mixedMoment B raw7801step1 raw7801step1Labels = mixedMoment B raw7801step2 raw7801step2Labels := by
      have ha : raw7801step2 = (fun i j => raw7801step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7801step2 raw7801step1; decide +kernel
      have hl : raw7801step2Labels = raw7801step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7801step1 raw7801step1Labels permutation12 permutation2
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw7802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw7802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7802 raw7802Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw7802 raw7802Labels = mixedMoment B raw7802step0 raw7802step0Labels := by
      have hz : ∀ j, raw7802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7802step0 = (fun i j => raw7802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7802step0 raw7802; decide +kernel
      have hl : raw7802step0Labels = raw7802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7802 raw7802Labels permutation434 hz
    mixedMoment B raw7802step0 raw7802step0Labels = mixedMoment B raw7802step1 raw7802step1Labels := by
      have hz : ∀ j, raw7802step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7802step1 = (fun i j => raw7802step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7802step1 raw7802step0; decide +kernel
      have hl : raw7802step1Labels = raw7802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7802step0 raw7802step0Labels permutation80 hz
    mixedMoment B raw7802step1 raw7802step1Labels = mixedMoment B raw7802step2 raw7802step2Labels := by
      have ha : raw7802step2 = (fun i j => raw7802step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7802step2 raw7802step1; decide +kernel
      have hl : raw7802step2Labels = raw7802step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7802step1 raw7802step1Labels permutation9 permutation2
    _ = mixedMoment B node2603 node2603Labels := by rfl

def raw7803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw7803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7803 raw7803Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw7803 raw7803Labels = mixedMoment B raw7803step0 raw7803step0Labels := by
      have hz : ∀ j, raw7803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7803step0 = (fun i j => raw7803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7803step0 raw7803; decide +kernel
      have hl : raw7803step0Labels = raw7803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7803 raw7803Labels permutation434 hz
    mixedMoment B raw7803step0 raw7803step0Labels = mixedMoment B raw7803step1 raw7803step1Labels := by
      have hz : ∀ j, raw7803step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7803step1 = (fun i j => raw7803step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7803step1 raw7803step0; decide +kernel
      have hl : raw7803step1Labels = raw7803step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7803step0 raw7803step0Labels permutation56 hz
    mixedMoment B raw7803step1 raw7803step1Labels = mixedMoment B raw7803step2 raw7803step2Labels := by
      have ha : raw7803step2 = (fun i j => raw7803step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7803step2 raw7803step1; decide +kernel
      have hl : raw7803step2Labels = raw7803step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7803step1 raw7803step1Labels permutation9 permutation2
    _ = mixedMoment B node2603 node2603Labels := by rfl

def raw7804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw7804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7804 raw7804Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw7804 raw7804Labels = mixedMoment B raw7804step0 raw7804step0Labels := by
      have hz : ∀ j, raw7804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7804step0 = (fun i j => raw7804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7804step0 raw7804; decide +kernel
      have hl : raw7804step0Labels = raw7804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7804 raw7804Labels permutation346 hz
    mixedMoment B raw7804step0 raw7804step0Labels = mixedMoment B raw7804step1 raw7804step1Labels := by
      have hz : ∀ j, raw7804step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7804step1 = (fun i j => raw7804step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7804step1 raw7804step0; decide +kernel
      have hl : raw7804step1Labels = raw7804step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7804step0 raw7804step0Labels permutation56 hz
    mixedMoment B raw7804step1 raw7804step1Labels = mixedMoment B raw7804step2 raw7804step2Labels := by
      have ha : raw7804step2 = (fun i j => raw7804step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7804step2 raw7804step1; decide +kernel
      have hl : raw7804step2Labels = raw7804step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7804step1 raw7804step1Labels permutation9 permutation2
    _ = mixedMoment B node2603 node2603Labels := by rfl

def raw7805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7805step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 1, -3], ![1, -2, 1]]
def raw7805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7805step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7805step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7805 raw7805Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw7805 raw7805Labels = mixedMoment B raw7805step0 raw7805step0Labels := by
      have hz : ∀ j, raw7805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7805step0 = (fun i j => raw7805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7805step0 raw7805; decide +kernel
      have hl : raw7805step0Labels = raw7805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7805 raw7805Labels permutation434 hz
    mixedMoment B raw7805step0 raw7805step0Labels = mixedMoment B raw7805step1 raw7805step1Labels := by
      have hz : ∀ j, raw7805step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7805step1 = (fun i j => raw7805step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7805step1 raw7805step0; decide +kernel
      have hl : raw7805step1Labels = raw7805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7805step0 raw7805step0Labels permutation80 hz
    mixedMoment B raw7805step1 raw7805step1Labels = mixedMoment B raw7805step2 raw7805step2Labels := by
      have hz : ∀ j, raw7805step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7805step2 = (fun i j => raw7805step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7805step2 raw7805step1; decide +kernel
      have hl : raw7805step2Labels = raw7805step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7805step1 raw7805step1Labels permutation14 hz
    mixedMoment B raw7805step2 raw7805step2Labels = mixedMoment B raw7805step3 raw7805step3Labels := by
      have ha : raw7805step3 = (fun i j => raw7805step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7805step3 raw7805step2; decide +kernel
      have hl : raw7805step3Labels = raw7805step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7805step2 raw7805step2Labels permutation3 permutation2
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw7806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7806 raw7806Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw7806 raw7806Labels = mixedMoment B raw7806step0 raw7806step0Labels := by
      have hz : ∀ j, raw7806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7806step0 = (fun i j => raw7806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7806step0 raw7806; decide +kernel
      have hl : raw7806step0Labels = raw7806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7806 raw7806Labels permutation346 hz
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw7807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7807 raw7807Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw7807 raw7807Labels = mixedMoment B raw7807step0 raw7807step0Labels := by
      have hz : ∀ j, raw7807 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7807step0 = (fun i j => raw7807 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7807step0 raw7807; decide +kernel
      have hl : raw7807step0Labels = raw7807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7807 raw7807Labels permutation265 hz
    _ = mixedMoment B node5434 node5434Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
