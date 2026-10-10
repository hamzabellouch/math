import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41600Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41600step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41600 raw41600Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw41600 raw41600Labels = mixedMoment B raw41600step0 raw41600step0Labels := by
      have hz : ∀ j, raw41600 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41600step0 = (fun i j => raw41600 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41600step0 raw41600; decide +kernel
      have hl : raw41600step0Labels = raw41600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41600 raw41600Labels permutation265 hz
    mixedMoment B raw41600step0 raw41600step0Labels = mixedMoment B raw41600step1 raw41600step1Labels := by
      have ha : raw41600step1 = (fun i j => raw41600step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41600step1 raw41600step0; decide +kernel
      have hl : raw41600step1Labels = raw41600step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41600step0 raw41600step0Labels permutation37 permutation2
    mixedMoment B raw41600step1 raw41600step1Labels = mixedMoment B raw41600step2 raw41600step2Labels := by
      have ha : raw41600step2 = raw41600step1 := by apply Matrix.ext; unfold raw41600step2 raw41600step1; decide +kernel
      have hl : raw41600step1Labels = labelEmbedding1 ∘ raw41600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41600step1 raw41600step1Labels raw41600step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw41601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41601Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41601step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41601step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41601 raw41601Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw41601 raw41601Labels = mixedMoment B raw41601step0 raw41601step0Labels := by
      have hz : ∀ j, raw41601 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41601step0 = (fun i j => raw41601 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41601step0 raw41601; decide +kernel
      have hl : raw41601step0Labels = raw41601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41601 raw41601Labels permutation265 hz
    mixedMoment B raw41601step0 raw41601step0Labels = mixedMoment B raw41601step1 raw41601step1Labels := by
      have ha : raw41601step1 = (fun i j => raw41601step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41601step1 raw41601step0; decide +kernel
      have hl : raw41601step1Labels = raw41601step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41601step0 raw41601step0Labels permutation32 permutation3
    mixedMoment B raw41601step1 raw41601step1Labels = mixedMoment B raw41601step2 raw41601step2Labels := by
      have ha : raw41601step2 = raw41601step1 := by apply Matrix.ext; unfold raw41601step2 raw41601step1; decide +kernel
      have hl : raw41601step1Labels = labelEmbedding7 ∘ raw41601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41601step1 raw41601step1Labels raw41601step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw41602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41602Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41602step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41602 raw41602Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw41602 raw41602Labels = mixedMoment B raw41602step0 raw41602step0Labels := by
      have ha : raw41602step0 = (fun i j => raw41602 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41602step0 raw41602; decide +kernel
      have hl : raw41602step0Labels = raw41602Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41602 raw41602Labels permutation157 permutation2
    mixedMoment B raw41602step0 raw41602step0Labels = mixedMoment B raw41602step1 raw41602step1Labels := by
      have ha : raw41602step1 = raw41602step0 := by apply Matrix.ext; unfold raw41602step1 raw41602step0; decide +kernel
      have hl : raw41602step0Labels = labelEmbedding1 ∘ raw41602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41602step0 raw41602step0Labels raw41602step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw41603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41603Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41603step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41603 raw41603Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw41603 raw41603Labels = mixedMoment B raw41603step0 raw41603step0Labels := by
      have ha : raw41603step0 = (fun i j => raw41603 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41603step0 raw41603; decide +kernel
      have hl : raw41603step0Labels = raw41603Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41603 raw41603Labels permutation152 permutation3
    mixedMoment B raw41603step0 raw41603step0Labels = mixedMoment B raw41603step1 raw41603step1Labels := by
      have ha : raw41603step1 = raw41603step0 := by apply Matrix.ext; unfold raw41603step1 raw41603step0; decide +kernel
      have hl : raw41603step0Labels = labelEmbedding7 ∘ raw41603step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41603step0 raw41603step0Labels raw41603step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw41604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41604Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw41604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41604step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw41604step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41604step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw41604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41604 raw41604Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw41604 raw41604Labels = mixedMoment B raw41604step0 raw41604step0Labels := by
      have hz : ∀ j, raw41604 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41604step0 = (fun i j => raw41604 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41604step0 raw41604; decide +kernel
      have hl : raw41604step0Labels = raw41604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41604 raw41604Labels permutation520 hz
    mixedMoment B raw41604step0 raw41604step0Labels = mixedMoment B raw41604step1 raw41604step1Labels := by
      have hz : ∀ j, raw41604step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41604step1 = (fun i j => raw41604step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41604step1 raw41604step0; decide +kernel
      have hl : raw41604step1Labels = raw41604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41604step0 raw41604step0Labels permutation104 hz
    mixedMoment B raw41604step1 raw41604step1Labels = mixedMoment B raw41604step2 raw41604step2Labels := by
      have hz : ∀ j, raw41604step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41604step2 = (fun i j => raw41604step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41604step2 raw41604step1; decide +kernel
      have hl : raw41604step2Labels = raw41604step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41604step1 raw41604step1Labels permutation20 hz
    mixedMoment B raw41604step2 raw41604step2Labels = mixedMoment B raw41604step3 raw41604step3Labels := by
      have ha : raw41604step3 = raw41604step2 := by apply Matrix.ext; unfold raw41604step3 raw41604step2; decide +kernel
      have hl : raw41604step2Labels = labelEmbedding1 ∘ raw41604step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41604step2 raw41604step2Labels raw41604step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

def raw41605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41605Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41605step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw41605step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41605step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw41605step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41605step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw41605step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41605step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw41605step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41605step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw41605step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41605 raw41605Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw41605 raw41605Labels = mixedMoment B raw41605step0 raw41605step0Labels := by
      have hz : ∀ j, raw41605 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41605step0 = (fun i j => raw41605 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41605step0 raw41605; decide +kernel
      have hl : raw41605step0Labels = raw41605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41605 raw41605Labels permutation520 hz
    mixedMoment B raw41605step0 raw41605step0Labels = mixedMoment B raw41605step1 raw41605step1Labels := by
      have hz : ∀ j, raw41605step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41605step1 = (fun i j => raw41605step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41605step1 raw41605step0; decide +kernel
      have hl : raw41605step1Labels = raw41605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41605step0 raw41605step0Labels permutation104 hz
    mixedMoment B raw41605step1 raw41605step1Labels = mixedMoment B raw41605step2 raw41605step2Labels := by
      have hz : ∀ j, raw41605step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41605step2 = (fun i j => raw41605step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41605step2 raw41605step1; decide +kernel
      have hl : raw41605step2Labels = raw41605step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41605step1 raw41605step1Labels permutation20 hz
    mixedMoment B raw41605step2 raw41605step2Labels = mixedMoment B raw41605step3 raw41605step3Labels := by
      have ha : raw41605step3 = (fun i j => raw41605step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41605step3 raw41605step2; decide +kernel
      have hl : raw41605step3Labels = raw41605step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41605step2 raw41605step2Labels permutation7 permutation3
    mixedMoment B raw41605step3 raw41605step3Labels = mixedMoment B raw41605step4 raw41605step4Labels := by
      have ha : raw41605step4 = -raw41605step3 := by apply Matrix.ext; change ∀ i j, raw41605step4 i j = -(raw41605step3 i j); unfold raw41605step4 raw41605step3; decide +kernel
      have hl : raw41605step4Labels = raw41605step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41605step4 raw41605step4Labels = mixedMoment B raw41605step5 raw41605step5Labels := by
      have ha : raw41605step5 = raw41605step4 := by apply Matrix.ext; unfold raw41605step5 raw41605step4; decide +kernel
      have hl : raw41605step4Labels = labelEmbedding7 ∘ raw41605step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41605step4 raw41605step4Labels raw41605step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw41606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41606Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41606 raw41606Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw41606 raw41606Labels = mixedMoment B raw41606step0 raw41606step0Labels := by
      have hz : ∀ j, raw41606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41606step0 = (fun i j => raw41606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41606step0 raw41606; decide +kernel
      have hl : raw41606step0Labels = raw41606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41606 raw41606Labels permutation434 hz
    mixedMoment B raw41606step0 raw41606step0Labels = mixedMoment B raw41606step1 raw41606step1Labels := by
      have hz : ∀ j, raw41606step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41606step1 = (fun i j => raw41606step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41606step1 raw41606step0; decide +kernel
      have hl : raw41606step1Labels = raw41606step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41606step0 raw41606step0Labels permutation80 hz
    mixedMoment B raw41606step1 raw41606step1Labels = mixedMoment B raw41606step2 raw41606step2Labels := by
      have ha : raw41606step2 = raw41606step1 := by apply Matrix.ext; unfold raw41606step2 raw41606step1; decide +kernel
      have hl : raw41606step1Labels = labelEmbedding1 ∘ raw41606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41606step1 raw41606step1Labels raw41606step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw41607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41607Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41607step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41607step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41607step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41607 raw41607Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw41607 raw41607Labels = mixedMoment B raw41607step0 raw41607step0Labels := by
      have hz : ∀ j, raw41607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41607step0 = (fun i j => raw41607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41607step0 raw41607; decide +kernel
      have hl : raw41607step0Labels = raw41607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41607 raw41607Labels permutation434 hz
    mixedMoment B raw41607step0 raw41607step0Labels = mixedMoment B raw41607step1 raw41607step1Labels := by
      have hz : ∀ j, raw41607step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41607step1 = (fun i j => raw41607step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41607step1 raw41607step0; decide +kernel
      have hl : raw41607step1Labels = raw41607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41607step0 raw41607step0Labels permutation80 hz
    mixedMoment B raw41607step1 raw41607step1Labels = mixedMoment B raw41607step2 raw41607step2Labels := by
      have ha : raw41607step2 = (fun i j => raw41607step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41607step2 raw41607step1; decide +kernel
      have hl : raw41607step2Labels = raw41607step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41607step1 raw41607step1Labels permutation30 permutation5
    mixedMoment B raw41607step2 raw41607step2Labels = mixedMoment B raw41607step3 raw41607step3Labels := by
      have ha : raw41607step3 = raw41607step2 := by apply Matrix.ext; unfold raw41607step3 raw41607step2; decide +kernel
      have hl : raw41607step2Labels = labelEmbedding9 ∘ raw41607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41607step2 raw41607step2Labels raw41607step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw41608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41608Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41608 raw41608Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw41608 raw41608Labels = mixedMoment B raw41608step0 raw41608step0Labels := by
      have hz : ∀ j, raw41608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41608step0 = (fun i j => raw41608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41608step0 raw41608; decide +kernel
      have hl : raw41608step0Labels = raw41608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41608 raw41608Labels permutation434 hz
    mixedMoment B raw41608step0 raw41608step0Labels = mixedMoment B raw41608step1 raw41608step1Labels := by
      have hz : ∀ j, raw41608step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41608step1 = (fun i j => raw41608step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41608step1 raw41608step0; decide +kernel
      have hl : raw41608step1Labels = raw41608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41608step0 raw41608step0Labels permutation80 hz
    mixedMoment B raw41608step1 raw41608step1Labels = mixedMoment B raw41608step2 raw41608step2Labels := by
      have ha : raw41608step2 = raw41608step1 := by apply Matrix.ext; unfold raw41608step2 raw41608step1; decide +kernel
      have hl : raw41608step1Labels = labelEmbedding1 ∘ raw41608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41608step1 raw41608step1Labels raw41608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw41609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41609Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41609step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41609step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41609 raw41609Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw41609 raw41609Labels = mixedMoment B raw41609step0 raw41609step0Labels := by
      have hz : ∀ j, raw41609 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41609step0 = (fun i j => raw41609 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41609step0 raw41609; decide +kernel
      have hl : raw41609step0Labels = raw41609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41609 raw41609Labels permutation434 hz
    mixedMoment B raw41609step0 raw41609step0Labels = mixedMoment B raw41609step1 raw41609step1Labels := by
      have hz : ∀ j, raw41609step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41609step1 = (fun i j => raw41609step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41609step1 raw41609step0; decide +kernel
      have hl : raw41609step1Labels = raw41609step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41609step0 raw41609step0Labels permutation80 hz
    mixedMoment B raw41609step1 raw41609step1Labels = mixedMoment B raw41609step2 raw41609step2Labels := by
      have ha : raw41609step2 = raw41609step1 := by apply Matrix.ext; unfold raw41609step2 raw41609step1; decide +kernel
      have hl : raw41609step1Labels = labelEmbedding8 ∘ raw41609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41609step1 raw41609step1Labels raw41609step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw41610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41610Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41610step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41610 raw41610Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw41610 raw41610Labels = mixedMoment B raw41610step0 raw41610step0Labels := by
      have hz : ∀ j, raw41610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41610step0 = (fun i j => raw41610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41610step0 raw41610; decide +kernel
      have hl : raw41610step0Labels = raw41610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41610 raw41610Labels permutation434 hz
    mixedMoment B raw41610step0 raw41610step0Labels = mixedMoment B raw41610step1 raw41610step1Labels := by
      have hz : ∀ j, raw41610step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41610step1 = (fun i j => raw41610step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41610step1 raw41610step0; decide +kernel
      have hl : raw41610step1Labels = raw41610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41610step0 raw41610step0Labels permutation80 hz
    mixedMoment B raw41610step1 raw41610step1Labels = mixedMoment B raw41610step2 raw41610step2Labels := by
      have ha : raw41610step2 = raw41610step1 := by apply Matrix.ext; unfold raw41610step2 raw41610step1; decide +kernel
      have hl : raw41610step1Labels = labelEmbedding1 ∘ raw41610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41610step1 raw41610step1Labels raw41610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw41611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41611Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41611step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41611step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41611 raw41611Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw41611 raw41611Labels = mixedMoment B raw41611step0 raw41611step0Labels := by
      have hz : ∀ j, raw41611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41611step0 = (fun i j => raw41611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41611step0 raw41611; decide +kernel
      have hl : raw41611step0Labels = raw41611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41611 raw41611Labels permutation434 hz
    mixedMoment B raw41611step0 raw41611step0Labels = mixedMoment B raw41611step1 raw41611step1Labels := by
      have hz : ∀ j, raw41611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41611step1 = (fun i j => raw41611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41611step1 raw41611step0; decide +kernel
      have hl : raw41611step1Labels = raw41611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41611step0 raw41611step0Labels permutation80 hz
    mixedMoment B raw41611step1 raw41611step1Labels = mixedMoment B raw41611step2 raw41611step2Labels := by
      have ha : raw41611step2 = raw41611step1 := by apply Matrix.ext; unfold raw41611step2 raw41611step1; decide +kernel
      have hl : raw41611step1Labels = labelEmbedding8 ∘ raw41611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41611step1 raw41611step1Labels raw41611step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw41612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41612Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41612 raw41612Labels = mixedMoment B node2771 node2771Labels := by
  calc
    mixedMoment B raw41612 raw41612Labels = mixedMoment B raw41612step0 raw41612step0Labels := by
      have hz : ∀ j, raw41612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41612step0 = (fun i j => raw41612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41612step0 raw41612; decide +kernel
      have hl : raw41612step0Labels = raw41612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41612 raw41612Labels permutation434 hz
    mixedMoment B raw41612step0 raw41612step0Labels = mixedMoment B raw41612step1 raw41612step1Labels := by
      have hz : ∀ j, raw41612step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41612step1 = (fun i j => raw41612step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41612step1 raw41612step0; decide +kernel
      have hl : raw41612step1Labels = raw41612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41612step0 raw41612step0Labels permutation80 hz
    mixedMoment B raw41612step1 raw41612step1Labels = mixedMoment B raw41612step2 raw41612step2Labels := by
      have ha : raw41612step2 = raw41612step1 := by apply Matrix.ext; unfold raw41612step2 raw41612step1; decide +kernel
      have hl : raw41612step1Labels = labelEmbedding1 ∘ raw41612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41612step1 raw41612step1Labels raw41612step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2771 node2771Labels := by rfl

def raw41613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41613Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41613step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41613step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41613 raw41613Labels = mixedMoment B node5297 node5297Labels := by
  calc
    mixedMoment B raw41613 raw41613Labels = mixedMoment B raw41613step0 raw41613step0Labels := by
      have hz : ∀ j, raw41613 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41613step0 = (fun i j => raw41613 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41613step0 raw41613; decide +kernel
      have hl : raw41613step0Labels = raw41613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41613 raw41613Labels permutation434 hz
    mixedMoment B raw41613step0 raw41613step0Labels = mixedMoment B raw41613step1 raw41613step1Labels := by
      have hz : ∀ j, raw41613step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41613step1 = (fun i j => raw41613step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41613step1 raw41613step0; decide +kernel
      have hl : raw41613step1Labels = raw41613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41613step0 raw41613step0Labels permutation80 hz
    mixedMoment B raw41613step1 raw41613step1Labels = mixedMoment B raw41613step2 raw41613step2Labels := by
      have ha : raw41613step2 = raw41613step1 := by apply Matrix.ext; unfold raw41613step2 raw41613step1; decide +kernel
      have hl : raw41613step1Labels = labelEmbedding8 ∘ raw41613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41613step1 raw41613step1Labels raw41613step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5297 node5297Labels := by rfl

def raw41614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41614Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41614 raw41614Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw41614 raw41614Labels = mixedMoment B raw41614step0 raw41614step0Labels := by
      have hz : ∀ j, raw41614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41614step0 = (fun i j => raw41614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41614step0 raw41614; decide +kernel
      have hl : raw41614step0Labels = raw41614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41614 raw41614Labels permutation346 hz
    mixedMoment B raw41614step0 raw41614step0Labels = mixedMoment B raw41614step1 raw41614step1Labels := by
      have ha : raw41614step1 = (fun i j => raw41614step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41614step1 raw41614step0; decide +kernel
      have hl : raw41614step1Labels = raw41614step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41614step0 raw41614step0Labels permutation38 permutation2
    mixedMoment B raw41614step1 raw41614step1Labels = mixedMoment B raw41614step2 raw41614step2Labels := by
      have ha : raw41614step2 = raw41614step1 := by apply Matrix.ext; unfold raw41614step2 raw41614step1; decide +kernel
      have hl : raw41614step1Labels = labelEmbedding1 ∘ raw41614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41614step1 raw41614step1Labels raw41614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw41615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41615Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41615step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41615step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41615step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41615 raw41615Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw41615 raw41615Labels = mixedMoment B raw41615step0 raw41615step0Labels := by
      have hz : ∀ j, raw41615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41615step0 = (fun i j => raw41615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41615step0 raw41615; decide +kernel
      have hl : raw41615step0Labels = raw41615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41615 raw41615Labels permutation346 hz
    mixedMoment B raw41615step0 raw41615step0Labels = mixedMoment B raw41615step1 raw41615step1Labels := by
      have ha : raw41615step1 = (fun i j => raw41615step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41615step1 raw41615step0; decide +kernel
      have hl : raw41615step1Labels = raw41615step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41615step0 raw41615step0Labels permutation38 permutation2
    mixedMoment B raw41615step1 raw41615step1Labels = mixedMoment B raw41615step2 raw41615step2Labels := by
      have ha : raw41615step2 = raw41615step1 := by apply Matrix.ext; unfold raw41615step2 raw41615step1; decide +kernel
      have hl : raw41615step1Labels = labelEmbedding8 ∘ raw41615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41615step1 raw41615step1Labels raw41615step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw41616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41616Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41616 raw41616Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw41616 raw41616Labels = mixedMoment B raw41616step0 raw41616step0Labels := by
      have hz : ∀ j, raw41616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41616step0 = (fun i j => raw41616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41616step0 raw41616; decide +kernel
      have hl : raw41616step0Labels = raw41616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41616 raw41616Labels permutation346 hz
    mixedMoment B raw41616step0 raw41616step0Labels = mixedMoment B raw41616step1 raw41616step1Labels := by
      have ha : raw41616step1 = (fun i j => raw41616step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41616step1 raw41616step0; decide +kernel
      have hl : raw41616step1Labels = raw41616step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41616step0 raw41616step0Labels permutation38 permutation2
    mixedMoment B raw41616step1 raw41616step1Labels = mixedMoment B raw41616step2 raw41616step2Labels := by
      have ha : raw41616step2 = raw41616step1 := by apply Matrix.ext; unfold raw41616step2 raw41616step1; decide +kernel
      have hl : raw41616step1Labels = labelEmbedding1 ∘ raw41616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41616step1 raw41616step1Labels raw41616step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw41617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41617Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41617step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41617step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41617 raw41617Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw41617 raw41617Labels = mixedMoment B raw41617step0 raw41617step0Labels := by
      have hz : ∀ j, raw41617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41617step0 = (fun i j => raw41617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41617step0 raw41617; decide +kernel
      have hl : raw41617step0Labels = raw41617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41617 raw41617Labels permutation346 hz
    mixedMoment B raw41617step0 raw41617step0Labels = mixedMoment B raw41617step1 raw41617step1Labels := by
      have ha : raw41617step1 = (fun i j => raw41617step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41617step1 raw41617step0; decide +kernel
      have hl : raw41617step1Labels = raw41617step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41617step0 raw41617step0Labels permutation38 permutation2
    mixedMoment B raw41617step1 raw41617step1Labels = mixedMoment B raw41617step2 raw41617step2Labels := by
      have ha : raw41617step2 = raw41617step1 := by apply Matrix.ext; unfold raw41617step2 raw41617step1; decide +kernel
      have hl : raw41617step1Labels = labelEmbedding8 ∘ raw41617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41617step1 raw41617step1Labels raw41617step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw41618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41618Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41618 raw41618Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw41618 raw41618Labels = mixedMoment B raw41618step0 raw41618step0Labels := by
      have hz : ∀ j, raw41618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41618step0 = (fun i j => raw41618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41618step0 raw41618; decide +kernel
      have hl : raw41618step0Labels = raw41618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41618 raw41618Labels permutation346 hz
    mixedMoment B raw41618step0 raw41618step0Labels = mixedMoment B raw41618step1 raw41618step1Labels := by
      have ha : raw41618step1 = (fun i j => raw41618step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41618step1 raw41618step0; decide +kernel
      have hl : raw41618step1Labels = raw41618step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41618step0 raw41618step0Labels permutation38 permutation2
    mixedMoment B raw41618step1 raw41618step1Labels = mixedMoment B raw41618step2 raw41618step2Labels := by
      have ha : raw41618step2 = raw41618step1 := by apply Matrix.ext; unfold raw41618step2 raw41618step1; decide +kernel
      have hl : raw41618step1Labels = labelEmbedding1 ∘ raw41618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41618step1 raw41618step1Labels raw41618step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw41619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41619Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41619step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41619step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41619 raw41619Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw41619 raw41619Labels = mixedMoment B raw41619step0 raw41619step0Labels := by
      have hz : ∀ j, raw41619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41619step0 = (fun i j => raw41619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41619step0 raw41619; decide +kernel
      have hl : raw41619step0Labels = raw41619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41619 raw41619Labels permutation346 hz
    mixedMoment B raw41619step0 raw41619step0Labels = mixedMoment B raw41619step1 raw41619step1Labels := by
      have ha : raw41619step1 = (fun i j => raw41619step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41619step1 raw41619step0; decide +kernel
      have hl : raw41619step1Labels = raw41619step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41619step0 raw41619step0Labels permutation38 permutation2
    mixedMoment B raw41619step1 raw41619step1Labels = mixedMoment B raw41619step2 raw41619step2Labels := by
      have ha : raw41619step2 = raw41619step1 := by apply Matrix.ext; unfold raw41619step2 raw41619step1; decide +kernel
      have hl : raw41619step1Labels = labelEmbedding8 ∘ raw41619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41619step1 raw41619step1Labels raw41619step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw41620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41620Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41620 raw41620Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw41620 raw41620Labels = mixedMoment B raw41620step0 raw41620step0Labels := by
      have hz : ∀ j, raw41620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41620step0 = (fun i j => raw41620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41620step0 raw41620; decide +kernel
      have hl : raw41620step0Labels = raw41620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41620 raw41620Labels permutation346 hz
    mixedMoment B raw41620step0 raw41620step0Labels = mixedMoment B raw41620step1 raw41620step1Labels := by
      have ha : raw41620step1 = (fun i j => raw41620step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41620step1 raw41620step0; decide +kernel
      have hl : raw41620step1Labels = raw41620step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41620step0 raw41620step0Labels permutation38 permutation2
    mixedMoment B raw41620step1 raw41620step1Labels = mixedMoment B raw41620step2 raw41620step2Labels := by
      have ha : raw41620step2 = raw41620step1 := by apply Matrix.ext; unfold raw41620step2 raw41620step1; decide +kernel
      have hl : raw41620step1Labels = labelEmbedding1 ∘ raw41620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41620step1 raw41620step1Labels raw41620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw41621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41621Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41621step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41621step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41621 raw41621Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw41621 raw41621Labels = mixedMoment B raw41621step0 raw41621step0Labels := by
      have hz : ∀ j, raw41621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41621step0 = (fun i j => raw41621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41621step0 raw41621; decide +kernel
      have hl : raw41621step0Labels = raw41621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41621 raw41621Labels permutation346 hz
    mixedMoment B raw41621step0 raw41621step0Labels = mixedMoment B raw41621step1 raw41621step1Labels := by
      have ha : raw41621step1 = (fun i j => raw41621step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41621step1 raw41621step0; decide +kernel
      have hl : raw41621step1Labels = raw41621step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41621step0 raw41621step0Labels permutation38 permutation2
    mixedMoment B raw41621step1 raw41621step1Labels = mixedMoment B raw41621step2 raw41621step2Labels := by
      have ha : raw41621step2 = raw41621step1 := by apply Matrix.ext; unfold raw41621step2 raw41621step1; decide +kernel
      have hl : raw41621step1Labels = labelEmbedding8 ∘ raw41621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41621step1 raw41621step1Labels raw41621step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw41622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41622Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41622 raw41622Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw41622 raw41622Labels = mixedMoment B raw41622step0 raw41622step0Labels := by
      have hz : ∀ j, raw41622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41622step0 = (fun i j => raw41622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41622step0 raw41622; decide +kernel
      have hl : raw41622step0Labels = raw41622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41622 raw41622Labels permutation346 hz
    mixedMoment B raw41622step0 raw41622step0Labels = mixedMoment B raw41622step1 raw41622step1Labels := by
      have ha : raw41622step1 = (fun i j => raw41622step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41622step1 raw41622step0; decide +kernel
      have hl : raw41622step1Labels = raw41622step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41622step0 raw41622step0Labels permutation144 permutation4
    mixedMoment B raw41622step1 raw41622step1Labels = mixedMoment B raw41622step2 raw41622step2Labels := by
      have ha : raw41622step2 = raw41622step1 := by apply Matrix.ext; unfold raw41622step2 raw41622step1; decide +kernel
      have hl : raw41622step1Labels = labelEmbedding1 ∘ raw41622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41622step1 raw41622step1Labels raw41622step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw41623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41623Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41623step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41623step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw41623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41623 raw41623Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw41623 raw41623Labels = mixedMoment B raw41623step0 raw41623step0Labels := by
      have hz : ∀ j, raw41623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41623step0 = (fun i j => raw41623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41623step0 raw41623; decide +kernel
      have hl : raw41623step0Labels = raw41623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41623 raw41623Labels permutation346 hz
    mixedMoment B raw41623step0 raw41623step0Labels = mixedMoment B raw41623step1 raw41623step1Labels := by
      have ha : raw41623step1 = (fun i j => raw41623step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41623step1 raw41623step0; decide +kernel
      have hl : raw41623step1Labels = raw41623step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41623step0 raw41623step0Labels permutation144 permutation4
    mixedMoment B raw41623step1 raw41623step1Labels = mixedMoment B raw41623step2 raw41623step2Labels := by
      have ha : raw41623step2 = raw41623step1 := by apply Matrix.ext; unfold raw41623step2 raw41623step1; decide +kernel
      have hl : raw41623step1Labels = labelEmbedding10 ∘ raw41623step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41623step1 raw41623step1Labels raw41623step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw41624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41624Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41624 raw41624Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw41624 raw41624Labels = mixedMoment B raw41624step0 raw41624step0Labels := by
      have hz : ∀ j, raw41624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41624step0 = (fun i j => raw41624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41624step0 raw41624; decide +kernel
      have hl : raw41624step0Labels = raw41624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41624 raw41624Labels permutation346 hz
    mixedMoment B raw41624step0 raw41624step0Labels = mixedMoment B raw41624step1 raw41624step1Labels := by
      have ha : raw41624step1 = (fun i j => raw41624step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41624step1 raw41624step0; decide +kernel
      have hl : raw41624step1Labels = raw41624step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41624step0 raw41624step0Labels permutation37 permutation2
    mixedMoment B raw41624step1 raw41624step1Labels = mixedMoment B raw41624step2 raw41624step2Labels := by
      have ha : raw41624step2 = raw41624step1 := by apply Matrix.ext; unfold raw41624step2 raw41624step1; decide +kernel
      have hl : raw41624step1Labels = labelEmbedding1 ∘ raw41624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41624step1 raw41624step1Labels raw41624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw41625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41625Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41625step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41625step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41625 raw41625Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw41625 raw41625Labels = mixedMoment B raw41625step0 raw41625step0Labels := by
      have hz : ∀ j, raw41625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41625step0 = (fun i j => raw41625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41625step0 raw41625; decide +kernel
      have hl : raw41625step0Labels = raw41625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41625 raw41625Labels permutation346 hz
    mixedMoment B raw41625step0 raw41625step0Labels = mixedMoment B raw41625step1 raw41625step1Labels := by
      have ha : raw41625step1 = (fun i j => raw41625step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41625step1 raw41625step0; decide +kernel
      have hl : raw41625step1Labels = raw41625step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41625step0 raw41625step0Labels permutation37 permutation2
    mixedMoment B raw41625step1 raw41625step1Labels = mixedMoment B raw41625step2 raw41625step2Labels := by
      have ha : raw41625step2 = raw41625step1 := by apply Matrix.ext; unfold raw41625step2 raw41625step1; decide +kernel
      have hl : raw41625step1Labels = labelEmbedding8 ∘ raw41625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41625step1 raw41625step1Labels raw41625step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw41626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41626Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41626 raw41626Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw41626 raw41626Labels = mixedMoment B raw41626step0 raw41626step0Labels := by
      have hz : ∀ j, raw41626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41626step0 = (fun i j => raw41626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41626step0 raw41626; decide +kernel
      have hl : raw41626step0Labels = raw41626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41626 raw41626Labels permutation346 hz
    mixedMoment B raw41626step0 raw41626step0Labels = mixedMoment B raw41626step1 raw41626step1Labels := by
      have ha : raw41626step1 = raw41626step0 := by apply Matrix.ext; unfold raw41626step1 raw41626step0; decide +kernel
      have hl : raw41626step0Labels = labelEmbedding1 ∘ raw41626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41626step0 raw41626step0Labels raw41626step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2775 node2775Labels := by rfl

def raw41627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41627Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41627step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41627 raw41627Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw41627 raw41627Labels = mixedMoment B raw41627step0 raw41627step0Labels := by
      have hz : ∀ j, raw41627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41627step0 = (fun i j => raw41627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41627step0 raw41627; decide +kernel
      have hl : raw41627step0Labels = raw41627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41627 raw41627Labels permutation346 hz
    mixedMoment B raw41627step0 raw41627step0Labels = mixedMoment B raw41627step1 raw41627step1Labels := by
      have ha : raw41627step1 = raw41627step0 := by apply Matrix.ext; unfold raw41627step1 raw41627step0; decide +kernel
      have hl : raw41627step0Labels = labelEmbedding8 ∘ raw41627step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41627step0 raw41627step0Labels raw41627step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw41628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41628Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41628 raw41628Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw41628 raw41628Labels = mixedMoment B raw41628step0 raw41628step0Labels := by
      have ha : raw41628step0 = (fun i j => raw41628 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41628step0 raw41628; decide +kernel
      have hl : raw41628step0Labels = raw41628Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41628 raw41628Labels permutation182 permutation2
    mixedMoment B raw41628step0 raw41628step0Labels = mixedMoment B raw41628step1 raw41628step1Labels := by
      have ha : raw41628step1 = raw41628step0 := by apply Matrix.ext; unfold raw41628step1 raw41628step0; decide +kernel
      have hl : raw41628step0Labels = labelEmbedding1 ∘ raw41628step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41628step0 raw41628step0Labels raw41628step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw41629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41629Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41629step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41629 raw41629Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw41629 raw41629Labels = mixedMoment B raw41629step0 raw41629step0Labels := by
      have ha : raw41629step0 = (fun i j => raw41629 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41629step0 raw41629; decide +kernel
      have hl : raw41629step0Labels = raw41629Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41629 raw41629Labels permutation182 permutation2
    mixedMoment B raw41629step0 raw41629step0Labels = mixedMoment B raw41629step1 raw41629step1Labels := by
      have ha : raw41629step1 = raw41629step0 := by apply Matrix.ext; unfold raw41629step1 raw41629step0; decide +kernel
      have hl : raw41629step0Labels = labelEmbedding8 ∘ raw41629step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41629step0 raw41629step0Labels raw41629step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw41630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41630Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41630 raw41630Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw41630 raw41630Labels = mixedMoment B raw41630step0 raw41630step0Labels := by
      have ha : raw41630step0 = (fun i j => raw41630 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41630step0 raw41630; decide +kernel
      have hl : raw41630step0Labels = raw41630Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41630 raw41630Labels permutation180 permutation2
    mixedMoment B raw41630step0 raw41630step0Labels = mixedMoment B raw41630step1 raw41630step1Labels := by
      have ha : raw41630step1 = raw41630step0 := by apply Matrix.ext; unfold raw41630step1 raw41630step0; decide +kernel
      have hl : raw41630step0Labels = labelEmbedding1 ∘ raw41630step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41630step0 raw41630step0Labels raw41630step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw41631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41631Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41631step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41631 raw41631Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw41631 raw41631Labels = mixedMoment B raw41631step0 raw41631step0Labels := by
      have ha : raw41631step0 = (fun i j => raw41631 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41631step0 raw41631; decide +kernel
      have hl : raw41631step0Labels = raw41631Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41631 raw41631Labels permutation180 permutation2
    mixedMoment B raw41631step0 raw41631step0Labels = mixedMoment B raw41631step1 raw41631step1Labels := by
      have ha : raw41631step1 = raw41631step0 := by apply Matrix.ext; unfold raw41631step1 raw41631step0; decide +kernel
      have hl : raw41631step0Labels = labelEmbedding8 ∘ raw41631step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41631step0 raw41631step0Labels raw41631step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw41632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41632Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41632 raw41632Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw41632 raw41632Labels = mixedMoment B raw41632step0 raw41632step0Labels := by
      have ha : raw41632step0 = (fun i j => raw41632 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41632step0 raw41632; decide +kernel
      have hl : raw41632step0Labels = raw41632Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41632 raw41632Labels permutation179 permutation2
    mixedMoment B raw41632step0 raw41632step0Labels = mixedMoment B raw41632step1 raw41632step1Labels := by
      have ha : raw41632step1 = raw41632step0 := by apply Matrix.ext; unfold raw41632step1 raw41632step0; decide +kernel
      have hl : raw41632step0Labels = labelEmbedding1 ∘ raw41632step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41632step0 raw41632step0Labels raw41632step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw41633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41633Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41633step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41633 raw41633Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw41633 raw41633Labels = mixedMoment B raw41633step0 raw41633step0Labels := by
      have ha : raw41633step0 = (fun i j => raw41633 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41633step0 raw41633; decide +kernel
      have hl : raw41633step0Labels = raw41633Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41633 raw41633Labels permutation179 permutation2
    mixedMoment B raw41633step0 raw41633step0Labels = mixedMoment B raw41633step1 raw41633step1Labels := by
      have ha : raw41633step1 = raw41633step0 := by apply Matrix.ext; unfold raw41633step1 raw41633step0; decide +kernel
      have hl : raw41633step0Labels = labelEmbedding8 ∘ raw41633step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41633step0 raw41633step0Labels raw41633step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw41634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41634Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41634 raw41634Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw41634 raw41634Labels = mixedMoment B raw41634step0 raw41634step0Labels := by
      have ha : raw41634step0 = (fun i j => raw41634 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41634step0 raw41634; decide +kernel
      have hl : raw41634step0Labels = raw41634Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41634 raw41634Labels permutation180 permutation2
    mixedMoment B raw41634step0 raw41634step0Labels = mixedMoment B raw41634step1 raw41634step1Labels := by
      have ha : raw41634step1 = raw41634step0 := by apply Matrix.ext; unfold raw41634step1 raw41634step0; decide +kernel
      have hl : raw41634step0Labels = labelEmbedding1 ∘ raw41634step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41634step0 raw41634step0Labels raw41634step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw41635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41635Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41635step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41635 raw41635Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw41635 raw41635Labels = mixedMoment B raw41635step0 raw41635step0Labels := by
      have ha : raw41635step0 = (fun i j => raw41635 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41635step0 raw41635; decide +kernel
      have hl : raw41635step0Labels = raw41635Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41635 raw41635Labels permutation180 permutation2
    mixedMoment B raw41635step0 raw41635step0Labels = mixedMoment B raw41635step1 raw41635step1Labels := by
      have ha : raw41635step1 = raw41635step0 := by apply Matrix.ext; unfold raw41635step1 raw41635step0; decide +kernel
      have hl : raw41635step0Labels = labelEmbedding8 ∘ raw41635step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41635step0 raw41635step0Labels raw41635step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw41636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41636Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41636step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41636step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41636 raw41636Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw41636 raw41636Labels = mixedMoment B raw41636step0 raw41636step0Labels := by
      have hz : ∀ j, raw41636 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41636step0 = (fun i j => raw41636 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41636step0 raw41636; decide +kernel
      have hl : raw41636step0Labels = raw41636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41636 raw41636Labels permutation520 hz
    mixedMoment B raw41636step0 raw41636step0Labels = mixedMoment B raw41636step1 raw41636step1Labels := by
      have hz : ∀ j, raw41636step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41636step1 = (fun i j => raw41636step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41636step1 raw41636step0; decide +kernel
      have hl : raw41636step1Labels = raw41636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41636step0 raw41636step0Labels permutation104 hz
    mixedMoment B raw41636step1 raw41636step1Labels = mixedMoment B raw41636step2 raw41636step2Labels := by
      have ha : raw41636step2 = raw41636step1 := by apply Matrix.ext; unfold raw41636step2 raw41636step1; decide +kernel
      have hl : raw41636step1Labels = labelEmbedding1 ∘ raw41636step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41636step1 raw41636step1Labels raw41636step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw41637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41637Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41637step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41637step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw41637step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41637step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41637step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41637step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41637 raw41637Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw41637 raw41637Labels = mixedMoment B raw41637step0 raw41637step0Labels := by
      have hz : ∀ j, raw41637 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41637step0 = (fun i j => raw41637 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41637step0 raw41637; decide +kernel
      have hl : raw41637step0Labels = raw41637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41637 raw41637Labels permutation520 hz
    mixedMoment B raw41637step0 raw41637step0Labels = mixedMoment B raw41637step1 raw41637step1Labels := by
      have hz : ∀ j, raw41637step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41637step1 = (fun i j => raw41637step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41637step1 raw41637step0; decide +kernel
      have hl : raw41637step1Labels = raw41637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41637step0 raw41637step0Labels permutation104 hz
    mixedMoment B raw41637step1 raw41637step1Labels = mixedMoment B raw41637step2 raw41637step2Labels := by
      have ha : raw41637step2 = (fun i j => raw41637step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41637step2 raw41637step1; decide +kernel
      have hl : raw41637step2Labels = raw41637step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41637step1 raw41637step1Labels permutation29 permutation3
    mixedMoment B raw41637step2 raw41637step2Labels = mixedMoment B raw41637step3 raw41637step3Labels := by
      have ha : raw41637step3 = -raw41637step2 := by apply Matrix.ext; change ∀ i j, raw41637step3 i j = -(raw41637step2 i j); unfold raw41637step3 raw41637step2; decide +kernel
      have hl : raw41637step3Labels = raw41637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41637step3 raw41637step3Labels = mixedMoment B raw41637step4 raw41637step4Labels := by
      have ha : raw41637step4 = raw41637step3 := by apply Matrix.ext; unfold raw41637step4 raw41637step3; decide +kernel
      have hl : raw41637step3Labels = labelEmbedding7 ∘ raw41637step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41637step3 raw41637step3Labels raw41637step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw41638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41638Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41638step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41638 raw41638Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw41638 raw41638Labels = mixedMoment B raw41638step0 raw41638step0Labels := by
      have hz : ∀ j, raw41638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41638step0 = (fun i j => raw41638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41638step0 raw41638; decide +kernel
      have hl : raw41638step0Labels = raw41638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41638 raw41638Labels permutation434 hz
    mixedMoment B raw41638step0 raw41638step0Labels = mixedMoment B raw41638step1 raw41638step1Labels := by
      have ha : raw41638step1 = raw41638step0 := by apply Matrix.ext; unfold raw41638step1 raw41638step0; decide +kernel
      have hl : raw41638step0Labels = labelEmbedding1 ∘ raw41638step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41638step0 raw41638step0Labels raw41638step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw41639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41639Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41639step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41639step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41639 raw41639Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw41639 raw41639Labels = mixedMoment B raw41639step0 raw41639step0Labels := by
      have hz : ∀ j, raw41639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41639step0 = (fun i j => raw41639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41639step0 raw41639; decide +kernel
      have hl : raw41639step0Labels = raw41639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41639 raw41639Labels permutation434 hz
    mixedMoment B raw41639step0 raw41639step0Labels = mixedMoment B raw41639step1 raw41639step1Labels := by
      have ha : raw41639step1 = (fun i j => raw41639step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41639step1 raw41639step0; decide +kernel
      have hl : raw41639step1Labels = raw41639step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41639step0 raw41639step0Labels permutation149 permutation5
    mixedMoment B raw41639step1 raw41639step1Labels = mixedMoment B raw41639step2 raw41639step2Labels := by
      have ha : raw41639step2 = raw41639step1 := by apply Matrix.ext; unfold raw41639step2 raw41639step1; decide +kernel
      have hl : raw41639step1Labels = labelEmbedding9 ∘ raw41639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41639step1 raw41639step1Labels raw41639step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw41640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41640Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41640 raw41640Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw41640 raw41640Labels = mixedMoment B raw41640step0 raw41640step0Labels := by
      have hz : ∀ j, raw41640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41640step0 = (fun i j => raw41640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41640step0 raw41640; decide +kernel
      have hl : raw41640step0Labels = raw41640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41640 raw41640Labels permutation434 hz
    mixedMoment B raw41640step0 raw41640step0Labels = mixedMoment B raw41640step1 raw41640step1Labels := by
      have ha : raw41640step1 = raw41640step0 := by apply Matrix.ext; unfold raw41640step1 raw41640step0; decide +kernel
      have hl : raw41640step0Labels = labelEmbedding1 ∘ raw41640step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41640step0 raw41640step0Labels raw41640step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw41641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41641Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41641step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41641 raw41641Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw41641 raw41641Labels = mixedMoment B raw41641step0 raw41641step0Labels := by
      have hz : ∀ j, raw41641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41641step0 = (fun i j => raw41641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41641step0 raw41641; decide +kernel
      have hl : raw41641step0Labels = raw41641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41641 raw41641Labels permutation434 hz
    mixedMoment B raw41641step0 raw41641step0Labels = mixedMoment B raw41641step1 raw41641step1Labels := by
      have ha : raw41641step1 = raw41641step0 := by apply Matrix.ext; unfold raw41641step1 raw41641step0; decide +kernel
      have hl : raw41641step0Labels = labelEmbedding8 ∘ raw41641step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41641step0 raw41641step0Labels raw41641step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw41642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41642Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41642step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41642 raw41642Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw41642 raw41642Labels = mixedMoment B raw41642step0 raw41642step0Labels := by
      have hz : ∀ j, raw41642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41642step0 = (fun i j => raw41642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41642step0 raw41642; decide +kernel
      have hl : raw41642step0Labels = raw41642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41642 raw41642Labels permutation434 hz
    mixedMoment B raw41642step0 raw41642step0Labels = mixedMoment B raw41642step1 raw41642step1Labels := by
      have ha : raw41642step1 = raw41642step0 := by apply Matrix.ext; unfold raw41642step1 raw41642step0; decide +kernel
      have hl : raw41642step0Labels = labelEmbedding1 ∘ raw41642step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41642step0 raw41642step0Labels raw41642step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw41643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41643Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41643step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41643 raw41643Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw41643 raw41643Labels = mixedMoment B raw41643step0 raw41643step0Labels := by
      have hz : ∀ j, raw41643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41643step0 = (fun i j => raw41643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41643step0 raw41643; decide +kernel
      have hl : raw41643step0Labels = raw41643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41643 raw41643Labels permutation434 hz
    mixedMoment B raw41643step0 raw41643step0Labels = mixedMoment B raw41643step1 raw41643step1Labels := by
      have ha : raw41643step1 = raw41643step0 := by apply Matrix.ext; unfold raw41643step1 raw41643step0; decide +kernel
      have hl : raw41643step0Labels = labelEmbedding8 ∘ raw41643step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41643step0 raw41643step0Labels raw41643step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw41644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41644Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41644 raw41644Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw41644 raw41644Labels = mixedMoment B raw41644step0 raw41644step0Labels := by
      have hz : ∀ j, raw41644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41644step0 = (fun i j => raw41644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41644step0 raw41644; decide +kernel
      have hl : raw41644step0Labels = raw41644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41644 raw41644Labels permutation434 hz
    mixedMoment B raw41644step0 raw41644step0Labels = mixedMoment B raw41644step1 raw41644step1Labels := by
      have ha : raw41644step1 = raw41644step0 := by apply Matrix.ext; unfold raw41644step1 raw41644step0; decide +kernel
      have hl : raw41644step0Labels = labelEmbedding1 ∘ raw41644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41644step0 raw41644step0Labels raw41644step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw41645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41645Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41645step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41645 raw41645Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw41645 raw41645Labels = mixedMoment B raw41645step0 raw41645step0Labels := by
      have hz : ∀ j, raw41645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41645step0 = (fun i j => raw41645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41645step0 raw41645; decide +kernel
      have hl : raw41645step0Labels = raw41645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41645 raw41645Labels permutation434 hz
    mixedMoment B raw41645step0 raw41645step0Labels = mixedMoment B raw41645step1 raw41645step1Labels := by
      have ha : raw41645step1 = raw41645step0 := by apply Matrix.ext; unfold raw41645step1 raw41645step0; decide +kernel
      have hl : raw41645step0Labels = labelEmbedding8 ∘ raw41645step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41645step0 raw41645step0Labels raw41645step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw41646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41646Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41646 raw41646Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw41646 raw41646Labels = mixedMoment B raw41646step0 raw41646step0Labels := by
      have ha : raw41646step0 = (fun i j => raw41646 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41646step0 raw41646; decide +kernel
      have hl : raw41646step0Labels = raw41646Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41646 raw41646Labels permutation200 permutation2
    mixedMoment B raw41646step0 raw41646step0Labels = mixedMoment B raw41646step1 raw41646step1Labels := by
      have ha : raw41646step1 = raw41646step0 := by apply Matrix.ext; unfold raw41646step1 raw41646step0; decide +kernel
      have hl : raw41646step0Labels = labelEmbedding1 ∘ raw41646step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41646step0 raw41646step0Labels raw41646step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw41647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41647Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41647step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41647 raw41647Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw41647 raw41647Labels = mixedMoment B raw41647step0 raw41647step0Labels := by
      have ha : raw41647step0 = (fun i j => raw41647 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41647step0 raw41647; decide +kernel
      have hl : raw41647step0Labels = raw41647Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41647 raw41647Labels permutation200 permutation2
    mixedMoment B raw41647step0 raw41647step0Labels = mixedMoment B raw41647step1 raw41647step1Labels := by
      have ha : raw41647step1 = raw41647step0 := by apply Matrix.ext; unfold raw41647step1 raw41647step0; decide +kernel
      have hl : raw41647step0Labels = labelEmbedding8 ∘ raw41647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41647step0 raw41647step0Labels raw41647step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw41648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41648Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41648 raw41648Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw41648 raw41648Labels = mixedMoment B raw41648step0 raw41648step0Labels := by
      have ha : raw41648step0 = (fun i j => raw41648 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41648step0 raw41648; decide +kernel
      have hl : raw41648step0Labels = raw41648Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41648 raw41648Labels permutation200 permutation2
    mixedMoment B raw41648step0 raw41648step0Labels = mixedMoment B raw41648step1 raw41648step1Labels := by
      have ha : raw41648step1 = raw41648step0 := by apply Matrix.ext; unfold raw41648step1 raw41648step0; decide +kernel
      have hl : raw41648step0Labels = labelEmbedding1 ∘ raw41648step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41648step0 raw41648step0Labels raw41648step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw41649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41649Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41649step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41649 raw41649Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw41649 raw41649Labels = mixedMoment B raw41649step0 raw41649step0Labels := by
      have ha : raw41649step0 = (fun i j => raw41649 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41649step0 raw41649; decide +kernel
      have hl : raw41649step0Labels = raw41649Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41649 raw41649Labels permutation200 permutation2
    mixedMoment B raw41649step0 raw41649step0Labels = mixedMoment B raw41649step1 raw41649step1Labels := by
      have ha : raw41649step1 = raw41649step0 := by apply Matrix.ext; unfold raw41649step1 raw41649step0; decide +kernel
      have hl : raw41649step0Labels = labelEmbedding8 ∘ raw41649step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41649step0 raw41649step0Labels raw41649step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw41650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41650Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41650step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41650 raw41650Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw41650 raw41650Labels = mixedMoment B raw41650step0 raw41650step0Labels := by
      have ha : raw41650step0 = (fun i j => raw41650 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41650step0 raw41650; decide +kernel
      have hl : raw41650step0Labels = raw41650Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41650 raw41650Labels permutation200 permutation2
    mixedMoment B raw41650step0 raw41650step0Labels = mixedMoment B raw41650step1 raw41650step1Labels := by
      have ha : raw41650step1 = raw41650step0 := by apply Matrix.ext; unfold raw41650step1 raw41650step0; decide +kernel
      have hl : raw41650step0Labels = labelEmbedding1 ∘ raw41650step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41650step0 raw41650step0Labels raw41650step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw41651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41651Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41651step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41651 raw41651Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw41651 raw41651Labels = mixedMoment B raw41651step0 raw41651step0Labels := by
      have ha : raw41651step0 = (fun i j => raw41651 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41651step0 raw41651; decide +kernel
      have hl : raw41651step0Labels = raw41651Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41651 raw41651Labels permutation200 permutation2
    mixedMoment B raw41651step0 raw41651step0Labels = mixedMoment B raw41651step1 raw41651step1Labels := by
      have ha : raw41651step1 = raw41651step0 := by apply Matrix.ext; unfold raw41651step1 raw41651step0; decide +kernel
      have hl : raw41651step0Labels = labelEmbedding8 ∘ raw41651step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41651step0 raw41651step0Labels raw41651step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw41652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41652Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41652 raw41652Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw41652 raw41652Labels = mixedMoment B raw41652step0 raw41652step0Labels := by
      have ha : raw41652step0 = (fun i j => raw41652 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41652step0 raw41652; decide +kernel
      have hl : raw41652step0Labels = raw41652Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41652 raw41652Labels permutation156 permutation2
    mixedMoment B raw41652step0 raw41652step0Labels = mixedMoment B raw41652step1 raw41652step1Labels := by
      have ha : raw41652step1 = raw41652step0 := by apply Matrix.ext; unfold raw41652step1 raw41652step0; decide +kernel
      have hl : raw41652step0Labels = labelEmbedding1 ∘ raw41652step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41652step0 raw41652step0Labels raw41652step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2747 node2747Labels := by rfl

def raw41653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41653Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41653step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41653 raw41653Labels = mixedMoment B node5278 node5278Labels := by
  calc
    mixedMoment B raw41653 raw41653Labels = mixedMoment B raw41653step0 raw41653step0Labels := by
      have ha : raw41653step0 = (fun i j => raw41653 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41653step0 raw41653; decide +kernel
      have hl : raw41653step0Labels = raw41653Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41653 raw41653Labels permutation156 permutation2
    mixedMoment B raw41653step0 raw41653step0Labels = mixedMoment B raw41653step1 raw41653step1Labels := by
      have ha : raw41653step1 = raw41653step0 := by apply Matrix.ext; unfold raw41653step1 raw41653step0; decide +kernel
      have hl : raw41653step0Labels = labelEmbedding8 ∘ raw41653step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41653step0 raw41653step0Labels raw41653step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5278 node5278Labels := by rfl

def raw41654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41654Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41654step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41654 raw41654Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw41654 raw41654Labels = mixedMoment B raw41654step0 raw41654step0Labels := by
      have ha : raw41654step0 = (fun i j => raw41654 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41654step0 raw41654; decide +kernel
      have hl : raw41654step0Labels = raw41654Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41654 raw41654Labels permutation157 permutation2
    mixedMoment B raw41654step0 raw41654step0Labels = mixedMoment B raw41654step1 raw41654step1Labels := by
      have ha : raw41654step1 = raw41654step0 := by apply Matrix.ext; unfold raw41654step1 raw41654step0; decide +kernel
      have hl : raw41654step0Labels = labelEmbedding1 ∘ raw41654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41654step0 raw41654step0Labels raw41654step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw41655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41655Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41655step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41655 raw41655Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw41655 raw41655Labels = mixedMoment B raw41655step0 raw41655step0Labels := by
      have ha : raw41655step0 = (fun i j => raw41655 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41655step0 raw41655; decide +kernel
      have hl : raw41655step0Labels = raw41655Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41655 raw41655Labels permutation157 permutation2
    mixedMoment B raw41655step0 raw41655step0Labels = mixedMoment B raw41655step1 raw41655step1Labels := by
      have ha : raw41655step1 = raw41655step0 := by apply Matrix.ext; unfold raw41655step1 raw41655step0; decide +kernel
      have hl : raw41655step0Labels = labelEmbedding8 ∘ raw41655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41655step0 raw41655step0Labels raw41655step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw41656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41656Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41656step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41656step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41656 raw41656Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw41656 raw41656Labels = mixedMoment B raw41656step0 raw41656step0Labels := by
      have hz : ∀ j, raw41656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41656step0 = (fun i j => raw41656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41656step0 raw41656; decide +kernel
      have hl : raw41656step0Labels = raw41656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41656 raw41656Labels permutation434 hz
    mixedMoment B raw41656step0 raw41656step0Labels = mixedMoment B raw41656step1 raw41656step1Labels := by
      have hz : ∀ j, raw41656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41656step1 = (fun i j => raw41656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41656step1 raw41656step0; decide +kernel
      have hl : raw41656step1Labels = raw41656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41656step0 raw41656step0Labels permutation80 hz
    mixedMoment B raw41656step1 raw41656step1Labels = mixedMoment B raw41656step2 raw41656step2Labels := by
      have ha : raw41656step2 = raw41656step1 := by apply Matrix.ext; unfold raw41656step2 raw41656step1; decide +kernel
      have hl : raw41656step1Labels = labelEmbedding1 ∘ raw41656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41656step1 raw41656step1Labels raw41656step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw41657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41657Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41657step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41657step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41657 raw41657Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw41657 raw41657Labels = mixedMoment B raw41657step0 raw41657step0Labels := by
      have hz : ∀ j, raw41657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41657step0 = (fun i j => raw41657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41657step0 raw41657; decide +kernel
      have hl : raw41657step0Labels = raw41657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41657 raw41657Labels permutation434 hz
    mixedMoment B raw41657step0 raw41657step0Labels = mixedMoment B raw41657step1 raw41657step1Labels := by
      have hz : ∀ j, raw41657step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41657step1 = (fun i j => raw41657step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41657step1 raw41657step0; decide +kernel
      have hl : raw41657step1Labels = raw41657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41657step0 raw41657step0Labels permutation80 hz
    mixedMoment B raw41657step1 raw41657step1Labels = mixedMoment B raw41657step2 raw41657step2Labels := by
      have ha : raw41657step2 = raw41657step1 := by apply Matrix.ext; unfold raw41657step2 raw41657step1; decide +kernel
      have hl : raw41657step1Labels = labelEmbedding8 ∘ raw41657step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41657step1 raw41657step1Labels raw41657step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw41658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41658Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41658step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41658 raw41658Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw41658 raw41658Labels = mixedMoment B raw41658step0 raw41658step0Labels := by
      have hz : ∀ j, raw41658 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41658step0 = (fun i j => raw41658 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41658step0 raw41658; decide +kernel
      have hl : raw41658step0Labels = raw41658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41658 raw41658Labels permutation434 hz
    mixedMoment B raw41658step0 raw41658step0Labels = mixedMoment B raw41658step1 raw41658step1Labels := by
      have hz : ∀ j, raw41658step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41658step1 = (fun i j => raw41658step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41658step1 raw41658step0; decide +kernel
      have hl : raw41658step1Labels = raw41658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41658step0 raw41658step0Labels permutation80 hz
    mixedMoment B raw41658step1 raw41658step1Labels = mixedMoment B raw41658step2 raw41658step2Labels := by
      have ha : raw41658step2 = raw41658step1 := by apply Matrix.ext; unfold raw41658step2 raw41658step1; decide +kernel
      have hl : raw41658step1Labels = labelEmbedding1 ∘ raw41658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41658step1 raw41658step1Labels raw41658step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw41659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41659Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41659step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41659step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw41659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw41659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41659 raw41659Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw41659 raw41659Labels = mixedMoment B raw41659step0 raw41659step0Labels := by
      have hz : ∀ j, raw41659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41659step0 = (fun i j => raw41659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41659step0 raw41659; decide +kernel
      have hl : raw41659step0Labels = raw41659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41659 raw41659Labels permutation434 hz
    mixedMoment B raw41659step0 raw41659step0Labels = mixedMoment B raw41659step1 raw41659step1Labels := by
      have hz : ∀ j, raw41659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41659step1 = (fun i j => raw41659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41659step1 raw41659step0; decide +kernel
      have hl : raw41659step1Labels = raw41659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41659step0 raw41659step0Labels permutation80 hz
    mixedMoment B raw41659step1 raw41659step1Labels = mixedMoment B raw41659step2 raw41659step2Labels := by
      have ha : raw41659step2 = (fun i j => raw41659step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41659step2 raw41659step1; decide +kernel
      have hl : raw41659step2Labels = raw41659step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41659step1 raw41659step1Labels permutation29 permutation7
    mixedMoment B raw41659step2 raw41659step2Labels = mixedMoment B raw41659step3 raw41659step3Labels := by
      have ha : raw41659step3 = raw41659step2 := by apply Matrix.ext; unfold raw41659step3 raw41659step2; decide +kernel
      have hl : raw41659step2Labels = labelEmbedding6 ∘ raw41659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41659step2 raw41659step2Labels raw41659step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw41660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41660Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41660step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41660step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41660 raw41660Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw41660 raw41660Labels = mixedMoment B raw41660step0 raw41660step0Labels := by
      have hz : ∀ j, raw41660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41660step0 = (fun i j => raw41660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41660step0 raw41660; decide +kernel
      have hl : raw41660step0Labels = raw41660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41660 raw41660Labels permutation346 hz
    mixedMoment B raw41660step0 raw41660step0Labels = mixedMoment B raw41660step1 raw41660step1Labels := by
      have ha : raw41660step1 = (fun i j => raw41660step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41660step1 raw41660step0; decide +kernel
      have hl : raw41660step1Labels = raw41660step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41660step0 raw41660step0Labels permutation38 permutation2
    mixedMoment B raw41660step1 raw41660step1Labels = mixedMoment B raw41660step2 raw41660step2Labels := by
      have ha : raw41660step2 = raw41660step1 := by apply Matrix.ext; unfold raw41660step2 raw41660step1; decide +kernel
      have hl : raw41660step1Labels = labelEmbedding1 ∘ raw41660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41660step1 raw41660step1Labels raw41660step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw41661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41661Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41661step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41661step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41661 raw41661Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw41661 raw41661Labels = mixedMoment B raw41661step0 raw41661step0Labels := by
      have hz : ∀ j, raw41661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41661step0 = (fun i j => raw41661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41661step0 raw41661; decide +kernel
      have hl : raw41661step0Labels = raw41661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41661 raw41661Labels permutation346 hz
    mixedMoment B raw41661step0 raw41661step0Labels = mixedMoment B raw41661step1 raw41661step1Labels := by
      have ha : raw41661step1 = (fun i j => raw41661step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41661step1 raw41661step0; decide +kernel
      have hl : raw41661step1Labels = raw41661step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41661step0 raw41661step0Labels permutation38 permutation2
    mixedMoment B raw41661step1 raw41661step1Labels = mixedMoment B raw41661step2 raw41661step2Labels := by
      have ha : raw41661step2 = raw41661step1 := by apply Matrix.ext; unfold raw41661step2 raw41661step1; decide +kernel
      have hl : raw41661step1Labels = labelEmbedding8 ∘ raw41661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41661step1 raw41661step1Labels raw41661step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw41662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41662Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41662step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41662step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41662 raw41662Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw41662 raw41662Labels = mixedMoment B raw41662step0 raw41662step0Labels := by
      have hz : ∀ j, raw41662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41662step0 = (fun i j => raw41662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41662step0 raw41662; decide +kernel
      have hl : raw41662step0Labels = raw41662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41662 raw41662Labels permutation346 hz
    mixedMoment B raw41662step0 raw41662step0Labels = mixedMoment B raw41662step1 raw41662step1Labels := by
      have ha : raw41662step1 = (fun i j => raw41662step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41662step1 raw41662step0; decide +kernel
      have hl : raw41662step1Labels = raw41662step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41662step0 raw41662step0Labels permutation38 permutation2
    mixedMoment B raw41662step1 raw41662step1Labels = mixedMoment B raw41662step2 raw41662step2Labels := by
      have ha : raw41662step2 = raw41662step1 := by apply Matrix.ext; unfold raw41662step2 raw41662step1; decide +kernel
      have hl : raw41662step1Labels = labelEmbedding1 ∘ raw41662step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41662step1 raw41662step1Labels raw41662step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw41663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41663Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41663step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41663step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41663 raw41663Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw41663 raw41663Labels = mixedMoment B raw41663step0 raw41663step0Labels := by
      have hz : ∀ j, raw41663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41663step0 = (fun i j => raw41663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41663step0 raw41663; decide +kernel
      have hl : raw41663step0Labels = raw41663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41663 raw41663Labels permutation346 hz
    mixedMoment B raw41663step0 raw41663step0Labels = mixedMoment B raw41663step1 raw41663step1Labels := by
      have ha : raw41663step1 = (fun i j => raw41663step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41663step1 raw41663step0; decide +kernel
      have hl : raw41663step1Labels = raw41663step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41663step0 raw41663step0Labels permutation139 permutation7
    mixedMoment B raw41663step1 raw41663step1Labels = mixedMoment B raw41663step2 raw41663step2Labels := by
      have ha : raw41663step2 = raw41663step1 := by apply Matrix.ext; unfold raw41663step2 raw41663step1; decide +kernel
      have hl : raw41663step1Labels = labelEmbedding6 ∘ raw41663step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41663step1 raw41663step1Labels raw41663step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw41664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41664Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41664step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41664step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41664 raw41664Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw41664 raw41664Labels = mixedMoment B raw41664step0 raw41664step0Labels := by
      have hz : ∀ j, raw41664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41664step0 = (fun i j => raw41664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41664step0 raw41664; decide +kernel
      have hl : raw41664step0Labels = raw41664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41664 raw41664Labels permutation346 hz
    mixedMoment B raw41664step0 raw41664step0Labels = mixedMoment B raw41664step1 raw41664step1Labels := by
      have ha : raw41664step1 = (fun i j => raw41664step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41664step1 raw41664step0; decide +kernel
      have hl : raw41664step1Labels = raw41664step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41664step0 raw41664step0Labels permutation38 permutation2
    mixedMoment B raw41664step1 raw41664step1Labels = mixedMoment B raw41664step2 raw41664step2Labels := by
      have ha : raw41664step2 = raw41664step1 := by apply Matrix.ext; unfold raw41664step2 raw41664step1; decide +kernel
      have hl : raw41664step1Labels = labelEmbedding1 ∘ raw41664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41664step1 raw41664step1Labels raw41664step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw41665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41665Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41665step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41665step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41665 raw41665Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw41665 raw41665Labels = mixedMoment B raw41665step0 raw41665step0Labels := by
      have hz : ∀ j, raw41665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41665step0 = (fun i j => raw41665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41665step0 raw41665; decide +kernel
      have hl : raw41665step0Labels = raw41665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41665 raw41665Labels permutation346 hz
    mixedMoment B raw41665step0 raw41665step0Labels = mixedMoment B raw41665step1 raw41665step1Labels := by
      have ha : raw41665step1 = (fun i j => raw41665step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41665step1 raw41665step0; decide +kernel
      have hl : raw41665step1Labels = raw41665step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41665step0 raw41665step0Labels permutation139 permutation7
    mixedMoment B raw41665step1 raw41665step1Labels = mixedMoment B raw41665step2 raw41665step2Labels := by
      have ha : raw41665step2 = raw41665step1 := by apply Matrix.ext; unfold raw41665step2 raw41665step1; decide +kernel
      have hl : raw41665step1Labels = labelEmbedding6 ∘ raw41665step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41665step1 raw41665step1Labels raw41665step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw41666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41666Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41666step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41666step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41666 raw41666Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw41666 raw41666Labels = mixedMoment B raw41666step0 raw41666step0Labels := by
      have hz : ∀ j, raw41666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41666step0 = (fun i j => raw41666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41666step0 raw41666; decide +kernel
      have hl : raw41666step0Labels = raw41666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41666 raw41666Labels permutation346 hz
    mixedMoment B raw41666step0 raw41666step0Labels = mixedMoment B raw41666step1 raw41666step1Labels := by
      have ha : raw41666step1 = (fun i j => raw41666step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41666step1 raw41666step0; decide +kernel
      have hl : raw41666step1Labels = raw41666step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41666step0 raw41666step0Labels permutation37 permutation2
    mixedMoment B raw41666step1 raw41666step1Labels = mixedMoment B raw41666step2 raw41666step2Labels := by
      have ha : raw41666step2 = raw41666step1 := by apply Matrix.ext; unfold raw41666step2 raw41666step1; decide +kernel
      have hl : raw41666step1Labels = labelEmbedding1 ∘ raw41666step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41666step1 raw41666step1Labels raw41666step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw41667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41667Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41667step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41667step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41667 raw41667Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw41667 raw41667Labels = mixedMoment B raw41667step0 raw41667step0Labels := by
      have hz : ∀ j, raw41667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41667step0 = (fun i j => raw41667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41667step0 raw41667; decide +kernel
      have hl : raw41667step0Labels = raw41667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41667 raw41667Labels permutation346 hz
    mixedMoment B raw41667step0 raw41667step0Labels = mixedMoment B raw41667step1 raw41667step1Labels := by
      have ha : raw41667step1 = (fun i j => raw41667step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41667step1 raw41667step0; decide +kernel
      have hl : raw41667step1Labels = raw41667step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41667step0 raw41667step0Labels permutation37 permutation2
    mixedMoment B raw41667step1 raw41667step1Labels = mixedMoment B raw41667step2 raw41667step2Labels := by
      have ha : raw41667step2 = raw41667step1 := by apply Matrix.ext; unfold raw41667step2 raw41667step1; decide +kernel
      have hl : raw41667step1Labels = labelEmbedding8 ∘ raw41667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41667step1 raw41667step1Labels raw41667step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw41668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41668Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41668step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41668step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41668 raw41668Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw41668 raw41668Labels = mixedMoment B raw41668step0 raw41668step0Labels := by
      have hz : ∀ j, raw41668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41668step0 = (fun i j => raw41668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41668step0 raw41668; decide +kernel
      have hl : raw41668step0Labels = raw41668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41668 raw41668Labels permutation346 hz
    mixedMoment B raw41668step0 raw41668step0Labels = mixedMoment B raw41668step1 raw41668step1Labels := by
      have ha : raw41668step1 = (fun i j => raw41668step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41668step1 raw41668step0; decide +kernel
      have hl : raw41668step1Labels = raw41668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41668step0 raw41668step0Labels permutation37 permutation2
    mixedMoment B raw41668step1 raw41668step1Labels = mixedMoment B raw41668step2 raw41668step2Labels := by
      have ha : raw41668step2 = raw41668step1 := by apply Matrix.ext; unfold raw41668step2 raw41668step1; decide +kernel
      have hl : raw41668step1Labels = labelEmbedding1 ∘ raw41668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41668step1 raw41668step1Labels raw41668step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw41669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41669Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41669step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41669step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41669 raw41669Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw41669 raw41669Labels = mixedMoment B raw41669step0 raw41669step0Labels := by
      have hz : ∀ j, raw41669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41669step0 = (fun i j => raw41669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41669step0 raw41669; decide +kernel
      have hl : raw41669step0Labels = raw41669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41669 raw41669Labels permutation346 hz
    mixedMoment B raw41669step0 raw41669step0Labels = mixedMoment B raw41669step1 raw41669step1Labels := by
      have ha : raw41669step1 = (fun i j => raw41669step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41669step1 raw41669step0; decide +kernel
      have hl : raw41669step1Labels = raw41669step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41669step0 raw41669step0Labels permutation37 permutation2
    mixedMoment B raw41669step1 raw41669step1Labels = mixedMoment B raw41669step2 raw41669step2Labels := by
      have ha : raw41669step2 = raw41669step1 := by apply Matrix.ext; unfold raw41669step2 raw41669step1; decide +kernel
      have hl : raw41669step1Labels = labelEmbedding8 ∘ raw41669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41669step1 raw41669step1Labels raw41669step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw41670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41670Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41670step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41670 raw41670Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw41670 raw41670Labels = mixedMoment B raw41670step0 raw41670step0Labels := by
      have ha : raw41670step0 = (fun i j => raw41670 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41670step0 raw41670; decide +kernel
      have hl : raw41670step0Labels = raw41670Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41670 raw41670Labels permutation181 permutation2
    mixedMoment B raw41670step0 raw41670step0Labels = mixedMoment B raw41670step1 raw41670step1Labels := by
      have ha : raw41670step1 = raw41670step0 := by apply Matrix.ext; unfold raw41670step1 raw41670step0; decide +kernel
      have hl : raw41670step0Labels = labelEmbedding1 ∘ raw41670step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41670step0 raw41670step0Labels raw41670step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw41671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41671Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41671step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41671 raw41671Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw41671 raw41671Labels = mixedMoment B raw41671step0 raw41671step0Labels := by
      have ha : raw41671step0 = (fun i j => raw41671 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41671step0 raw41671; decide +kernel
      have hl : raw41671step0Labels = raw41671Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41671 raw41671Labels permutation181 permutation2
    mixedMoment B raw41671step0 raw41671step0Labels = mixedMoment B raw41671step1 raw41671step1Labels := by
      have ha : raw41671step1 = raw41671step0 := by apply Matrix.ext; unfold raw41671step1 raw41671step0; decide +kernel
      have hl : raw41671step0Labels = labelEmbedding8 ∘ raw41671step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41671step0 raw41671step0Labels raw41671step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw41672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41672Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41672step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41672 raw41672Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw41672 raw41672Labels = mixedMoment B raw41672step0 raw41672step0Labels := by
      have ha : raw41672step0 = (fun i j => raw41672 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41672step0 raw41672; decide +kernel
      have hl : raw41672step0Labels = raw41672Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41672 raw41672Labels permutation181 permutation2
    mixedMoment B raw41672step0 raw41672step0Labels = mixedMoment B raw41672step1 raw41672step1Labels := by
      have ha : raw41672step1 = raw41672step0 := by apply Matrix.ext; unfold raw41672step1 raw41672step0; decide +kernel
      have hl : raw41672step0Labels = labelEmbedding1 ∘ raw41672step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41672step0 raw41672step0Labels raw41672step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw41673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41673Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41673step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41673 raw41673Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw41673 raw41673Labels = mixedMoment B raw41673step0 raw41673step0Labels := by
      have ha : raw41673step0 = (fun i j => raw41673 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41673step0 raw41673; decide +kernel
      have hl : raw41673step0Labels = raw41673Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41673 raw41673Labels permutation181 permutation2
    mixedMoment B raw41673step0 raw41673step0Labels = mixedMoment B raw41673step1 raw41673step1Labels := by
      have ha : raw41673step1 = raw41673step0 := by apply Matrix.ext; unfold raw41673step1 raw41673step0; decide +kernel
      have hl : raw41673step0Labels = labelEmbedding8 ∘ raw41673step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41673step0 raw41673step0Labels raw41673step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw41674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41674Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41674step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41674step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41674step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41674step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41674step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41674step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41674 raw41674Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw41674 raw41674Labels = mixedMoment B raw41674step0 raw41674step0Labels := by
      have hz : ∀ j, raw41674 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41674step0 = (fun i j => raw41674 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41674step0 raw41674; decide +kernel
      have hl : raw41674step0Labels = raw41674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41674 raw41674Labels permutation434 hz
    mixedMoment B raw41674step0 raw41674step0Labels = mixedMoment B raw41674step1 raw41674step1Labels := by
      have hz : ∀ j, raw41674step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41674step1 = (fun i j => raw41674step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41674step1 raw41674step0; decide +kernel
      have hl : raw41674step1Labels = raw41674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41674step0 raw41674step0Labels permutation80 hz
    mixedMoment B raw41674step1 raw41674step1Labels = mixedMoment B raw41674step2 raw41674step2Labels := by
      have hz : ∀ j, raw41674step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41674step2 = (fun i j => raw41674step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41674step2 raw41674step1; decide +kernel
      have hl : raw41674step2Labels = raw41674step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41674step1 raw41674step1Labels permutation14 hz
    mixedMoment B raw41674step2 raw41674step2Labels = mixedMoment B raw41674step3 raw41674step3Labels := by
      have ha : raw41674step3 = raw41674step2 := by apply Matrix.ext; unfold raw41674step3 raw41674step2; decide +kernel
      have hl : raw41674step2Labels = labelEmbedding1 ∘ raw41674step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41674step2 raw41674step2Labels raw41674step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw41675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41675Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41675step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41675step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41675step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41675step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41675step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41675 raw41675Labels = mixedMoment B node5311 node5311Labels := by
  calc
    mixedMoment B raw41675 raw41675Labels = mixedMoment B raw41675step0 raw41675step0Labels := by
      have hz : ∀ j, raw41675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41675step0 = (fun i j => raw41675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41675step0 raw41675; decide +kernel
      have hl : raw41675step0Labels = raw41675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41675 raw41675Labels permutation434 hz
    mixedMoment B raw41675step0 raw41675step0Labels = mixedMoment B raw41675step1 raw41675step1Labels := by
      have hz : ∀ j, raw41675step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41675step1 = (fun i j => raw41675step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41675step1 raw41675step0; decide +kernel
      have hl : raw41675step1Labels = raw41675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41675step0 raw41675step0Labels permutation80 hz
    mixedMoment B raw41675step1 raw41675step1Labels = mixedMoment B raw41675step2 raw41675step2Labels := by
      have hz : ∀ j, raw41675step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41675step2 = (fun i j => raw41675step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41675step2 raw41675step1; decide +kernel
      have hl : raw41675step2Labels = raw41675step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41675step1 raw41675step1Labels permutation14 hz
    mixedMoment B raw41675step2 raw41675step2Labels = mixedMoment B raw41675step3 raw41675step3Labels := by
      have ha : raw41675step3 = raw41675step2 := by apply Matrix.ext; unfold raw41675step3 raw41675step2; decide +kernel
      have hl : raw41675step2Labels = labelEmbedding8 ∘ raw41675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41675step2 raw41675step2Labels raw41675step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5311 node5311Labels := by rfl

def raw41676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41676Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41676step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41676step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41676step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw41676step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41676step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw41676step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41676 raw41676Labels = mixedMoment B node2780 node2780Labels := by
  calc
    mixedMoment B raw41676 raw41676Labels = mixedMoment B raw41676step0 raw41676step0Labels := by
      have hz : ∀ j, raw41676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41676step0 = (fun i j => raw41676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41676step0 raw41676; decide +kernel
      have hl : raw41676step0Labels = raw41676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41676 raw41676Labels permutation434 hz
    mixedMoment B raw41676step0 raw41676step0Labels = mixedMoment B raw41676step1 raw41676step1Labels := by
      have hz : ∀ j, raw41676step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41676step1 = (fun i j => raw41676step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41676step1 raw41676step0; decide +kernel
      have hl : raw41676step1Labels = raw41676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41676step0 raw41676step0Labels permutation80 hz
    mixedMoment B raw41676step1 raw41676step1Labels = mixedMoment B raw41676step2 raw41676step2Labels := by
      have hz : ∀ j, raw41676step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41676step2 = (fun i j => raw41676step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41676step2 raw41676step1; decide +kernel
      have hl : raw41676step2Labels = raw41676step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41676step1 raw41676step1Labels permutation14 hz
    mixedMoment B raw41676step2 raw41676step2Labels = mixedMoment B raw41676step3 raw41676step3Labels := by
      have ha : raw41676step3 = raw41676step2 := by apply Matrix.ext; unfold raw41676step3 raw41676step2; decide +kernel
      have hl : raw41676step2Labels = labelEmbedding1 ∘ raw41676step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41676step2 raw41676step2Labels raw41676step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2780 node2780Labels := by rfl

def raw41677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41677Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41677step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41677step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41677step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw41677step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41677step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw41677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41677 raw41677Labels = mixedMoment B node4626 node4626Labels := by
  calc
    mixedMoment B raw41677 raw41677Labels = mixedMoment B raw41677step0 raw41677step0Labels := by
      have hz : ∀ j, raw41677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41677step0 = (fun i j => raw41677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41677step0 raw41677; decide +kernel
      have hl : raw41677step0Labels = raw41677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41677 raw41677Labels permutation434 hz
    mixedMoment B raw41677step0 raw41677step0Labels = mixedMoment B raw41677step1 raw41677step1Labels := by
      have hz : ∀ j, raw41677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41677step1 = (fun i j => raw41677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41677step1 raw41677step0; decide +kernel
      have hl : raw41677step1Labels = raw41677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41677step0 raw41677step0Labels permutation80 hz
    mixedMoment B raw41677step1 raw41677step1Labels = mixedMoment B raw41677step2 raw41677step2Labels := by
      have hz : ∀ j, raw41677step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41677step2 = (fun i j => raw41677step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41677step2 raw41677step1; decide +kernel
      have hl : raw41677step2Labels = raw41677step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41677step1 raw41677step1Labels permutation14 hz
    mixedMoment B raw41677step2 raw41677step2Labels = mixedMoment B raw41677step3 raw41677step3Labels := by
      have ha : raw41677step3 = (fun i j => raw41677step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41677step3 raw41677step2; decide +kernel
      have hl : raw41677step3Labels = raw41677step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41677step2 raw41677step2Labels permutation6 permutation6
    _ = mixedMoment B node4626 node4626Labels := by rfl

def raw41678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41678Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41678step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41678step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41678 raw41678Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw41678 raw41678Labels = mixedMoment B raw41678step0 raw41678step0Labels := by
      have hz : ∀ j, raw41678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41678step0 = (fun i j => raw41678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41678step0 raw41678; decide +kernel
      have hl : raw41678step0Labels = raw41678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41678 raw41678Labels permutation346 hz
    mixedMoment B raw41678step0 raw41678step0Labels = mixedMoment B raw41678step1 raw41678step1Labels := by
      have hz : ∀ j, raw41678step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41678step1 = (fun i j => raw41678step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41678step1 raw41678step0; decide +kernel
      have hl : raw41678step1Labels = raw41678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41678step0 raw41678step0Labels permutation56 hz
    mixedMoment B raw41678step1 raw41678step1Labels = mixedMoment B raw41678step2 raw41678step2Labels := by
      have ha : raw41678step2 = raw41678step1 := by apply Matrix.ext; unfold raw41678step2 raw41678step1; decide +kernel
      have hl : raw41678step1Labels = labelEmbedding1 ∘ raw41678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41678step1 raw41678step1Labels raw41678step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw41679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41679Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41679step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41679step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41679 raw41679Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw41679 raw41679Labels = mixedMoment B raw41679step0 raw41679step0Labels := by
      have hz : ∀ j, raw41679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41679step0 = (fun i j => raw41679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41679step0 raw41679; decide +kernel
      have hl : raw41679step0Labels = raw41679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41679 raw41679Labels permutation346 hz
    mixedMoment B raw41679step0 raw41679step0Labels = mixedMoment B raw41679step1 raw41679step1Labels := by
      have hz : ∀ j, raw41679step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41679step1 = (fun i j => raw41679step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41679step1 raw41679step0; decide +kernel
      have hl : raw41679step1Labels = raw41679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41679step0 raw41679step0Labels permutation56 hz
    mixedMoment B raw41679step1 raw41679step1Labels = mixedMoment B raw41679step2 raw41679step2Labels := by
      have ha : raw41679step2 = raw41679step1 := by apply Matrix.ext; unfold raw41679step2 raw41679step1; decide +kernel
      have hl : raw41679step1Labels = labelEmbedding8 ∘ raw41679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41679step1 raw41679step1Labels raw41679step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw41680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41680Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41680step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41680step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41680 raw41680Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw41680 raw41680Labels = mixedMoment B raw41680step0 raw41680step0Labels := by
      have hz : ∀ j, raw41680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41680step0 = (fun i j => raw41680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41680step0 raw41680; decide +kernel
      have hl : raw41680step0Labels = raw41680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41680 raw41680Labels permutation346 hz
    mixedMoment B raw41680step0 raw41680step0Labels = mixedMoment B raw41680step1 raw41680step1Labels := by
      have hz : ∀ j, raw41680step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41680step1 = (fun i j => raw41680step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41680step1 raw41680step0; decide +kernel
      have hl : raw41680step1Labels = raw41680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41680step0 raw41680step0Labels permutation56 hz
    mixedMoment B raw41680step1 raw41680step1Labels = mixedMoment B raw41680step2 raw41680step2Labels := by
      have ha : raw41680step2 = raw41680step1 := by apply Matrix.ext; unfold raw41680step2 raw41680step1; decide +kernel
      have hl : raw41680step1Labels = labelEmbedding1 ∘ raw41680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41680step1 raw41680step1Labels raw41680step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw41681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41681Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41681step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41681step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41681step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41681step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41681 raw41681Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw41681 raw41681Labels = mixedMoment B raw41681step0 raw41681step0Labels := by
      have hz : ∀ j, raw41681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41681step0 = (fun i j => raw41681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41681step0 raw41681; decide +kernel
      have hl : raw41681step0Labels = raw41681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41681 raw41681Labels permutation346 hz
    mixedMoment B raw41681step0 raw41681step0Labels = mixedMoment B raw41681step1 raw41681step1Labels := by
      have hz : ∀ j, raw41681step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41681step1 = (fun i j => raw41681step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41681step1 raw41681step0; decide +kernel
      have hl : raw41681step1Labels = raw41681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41681step0 raw41681step0Labels permutation56 hz
    mixedMoment B raw41681step1 raw41681step1Labels = mixedMoment B raw41681step2 raw41681step2Labels := by
      have ha : raw41681step2 = (fun i j => raw41681step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41681step2 raw41681step1; decide +kernel
      have hl : raw41681step2Labels = raw41681step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41681step1 raw41681step1Labels permutation31 permutation7
    mixedMoment B raw41681step2 raw41681step2Labels = mixedMoment B raw41681step3 raw41681step3Labels := by
      have ha : raw41681step3 = raw41681step2 := by apply Matrix.ext; unfold raw41681step3 raw41681step2; decide +kernel
      have hl : raw41681step2Labels = labelEmbedding6 ∘ raw41681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41681step2 raw41681step2Labels raw41681step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw41682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41682Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41682step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41682step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41682 raw41682Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw41682 raw41682Labels = mixedMoment B raw41682step0 raw41682step0Labels := by
      have hz : ∀ j, raw41682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41682step0 = (fun i j => raw41682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41682step0 raw41682; decide +kernel
      have hl : raw41682step0Labels = raw41682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41682 raw41682Labels permutation346 hz
    mixedMoment B raw41682step0 raw41682step0Labels = mixedMoment B raw41682step1 raw41682step1Labels := by
      have hz : ∀ j, raw41682step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41682step1 = (fun i j => raw41682step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41682step1 raw41682step0; decide +kernel
      have hl : raw41682step1Labels = raw41682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41682step0 raw41682step0Labels permutation56 hz
    mixedMoment B raw41682step1 raw41682step1Labels = mixedMoment B raw41682step2 raw41682step2Labels := by
      have ha : raw41682step2 = raw41682step1 := by apply Matrix.ext; unfold raw41682step2 raw41682step1; decide +kernel
      have hl : raw41682step1Labels = labelEmbedding1 ∘ raw41682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41682step1 raw41682step1Labels raw41682step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw41683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41683Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41683step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41683step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41683step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41683 raw41683Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw41683 raw41683Labels = mixedMoment B raw41683step0 raw41683step0Labels := by
      have hz : ∀ j, raw41683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41683step0 = (fun i j => raw41683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41683step0 raw41683; decide +kernel
      have hl : raw41683step0Labels = raw41683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41683 raw41683Labels permutation346 hz
    mixedMoment B raw41683step0 raw41683step0Labels = mixedMoment B raw41683step1 raw41683step1Labels := by
      have hz : ∀ j, raw41683step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41683step1 = (fun i j => raw41683step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41683step1 raw41683step0; decide +kernel
      have hl : raw41683step1Labels = raw41683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41683step0 raw41683step0Labels permutation56 hz
    mixedMoment B raw41683step1 raw41683step1Labels = mixedMoment B raw41683step2 raw41683step2Labels := by
      have ha : raw41683step2 = (fun i j => raw41683step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41683step2 raw41683step1; decide +kernel
      have hl : raw41683step2Labels = raw41683step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41683step1 raw41683step1Labels permutation31 permutation7
    mixedMoment B raw41683step2 raw41683step2Labels = mixedMoment B raw41683step3 raw41683step3Labels := by
      have ha : raw41683step3 = raw41683step2 := by apply Matrix.ext; unfold raw41683step3 raw41683step2; decide +kernel
      have hl : raw41683step2Labels = labelEmbedding6 ∘ raw41683step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41683step2 raw41683step2Labels raw41683step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw41684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41684Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41684step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41684step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41684step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41684step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41684 raw41684Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw41684 raw41684Labels = mixedMoment B raw41684step0 raw41684step0Labels := by
      have hz : ∀ j, raw41684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41684step0 = (fun i j => raw41684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41684step0 raw41684; decide +kernel
      have hl : raw41684step0Labels = raw41684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41684 raw41684Labels permutation346 hz
    mixedMoment B raw41684step0 raw41684step0Labels = mixedMoment B raw41684step1 raw41684step1Labels := by
      have hz : ∀ j, raw41684step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41684step1 = (fun i j => raw41684step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41684step1 raw41684step0; decide +kernel
      have hl : raw41684step1Labels = raw41684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41684step0 raw41684step0Labels permutation56 hz
    mixedMoment B raw41684step1 raw41684step1Labels = mixedMoment B raw41684step2 raw41684step2Labels := by
      have ha : raw41684step2 = (fun i j => raw41684step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41684step2 raw41684step1; decide +kernel
      have hl : raw41684step2Labels = raw41684step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41684step1 raw41684step1Labels permutation30 permutation4
    mixedMoment B raw41684step2 raw41684step2Labels = mixedMoment B raw41684step3 raw41684step3Labels := by
      have ha : raw41684step3 = raw41684step2 := by apply Matrix.ext; unfold raw41684step3 raw41684step2; decide +kernel
      have hl : raw41684step2Labels = labelEmbedding1 ∘ raw41684step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41684step2 raw41684step2Labels raw41684step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw41685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41685Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41685step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41685step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw41685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41685 raw41685Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw41685 raw41685Labels = mixedMoment B raw41685step0 raw41685step0Labels := by
      have hz : ∀ j, raw41685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41685step0 = (fun i j => raw41685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41685step0 raw41685; decide +kernel
      have hl : raw41685step0Labels = raw41685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41685 raw41685Labels permutation346 hz
    mixedMoment B raw41685step0 raw41685step0Labels = mixedMoment B raw41685step1 raw41685step1Labels := by
      have hz : ∀ j, raw41685step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41685step1 = (fun i j => raw41685step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41685step1 raw41685step0; decide +kernel
      have hl : raw41685step1Labels = raw41685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41685step0 raw41685step0Labels permutation56 hz
    mixedMoment B raw41685step1 raw41685step1Labels = mixedMoment B raw41685step2 raw41685step2Labels := by
      have ha : raw41685step2 = (fun i j => raw41685step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41685step2 raw41685step1; decide +kernel
      have hl : raw41685step2Labels = raw41685step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41685step1 raw41685step1Labels permutation16 permutation6
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw41686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41686Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41686step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41686step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41686step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41686step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41686step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41686 raw41686Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw41686 raw41686Labels = mixedMoment B raw41686step0 raw41686step0Labels := by
      have hz : ∀ j, raw41686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41686step0 = (fun i j => raw41686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41686step0 raw41686; decide +kernel
      have hl : raw41686step0Labels = raw41686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41686 raw41686Labels permutation346 hz
    mixedMoment B raw41686step0 raw41686step0Labels = mixedMoment B raw41686step1 raw41686step1Labels := by
      have hz : ∀ j, raw41686step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41686step1 = (fun i j => raw41686step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41686step1 raw41686step0; decide +kernel
      have hl : raw41686step1Labels = raw41686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41686step0 raw41686step0Labels permutation56 hz
    mixedMoment B raw41686step1 raw41686step1Labels = mixedMoment B raw41686step2 raw41686step2Labels := by
      have ha : raw41686step2 = (fun i j => raw41686step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41686step2 raw41686step1; decide +kernel
      have hl : raw41686step2Labels = raw41686step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41686step1 raw41686step1Labels permutation13 permutation2
    mixedMoment B raw41686step2 raw41686step2Labels = mixedMoment B raw41686step3 raw41686step3Labels := by
      have ha : raw41686step3 = raw41686step2 := by apply Matrix.ext; unfold raw41686step3 raw41686step2; decide +kernel
      have hl : raw41686step2Labels = labelEmbedding1 ∘ raw41686step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41686step2 raw41686step2Labels raw41686step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw41687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41687Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41687step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41687step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41687 raw41687Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw41687 raw41687Labels = mixedMoment B raw41687step0 raw41687step0Labels := by
      have hz : ∀ j, raw41687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41687step0 = (fun i j => raw41687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41687step0 raw41687; decide +kernel
      have hl : raw41687step0Labels = raw41687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41687 raw41687Labels permutation346 hz
    mixedMoment B raw41687step0 raw41687step0Labels = mixedMoment B raw41687step1 raw41687step1Labels := by
      have hz : ∀ j, raw41687step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41687step1 = (fun i j => raw41687step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41687step1 raw41687step0; decide +kernel
      have hl : raw41687step1Labels = raw41687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41687step0 raw41687step0Labels permutation56 hz
    mixedMoment B raw41687step1 raw41687step1Labels = mixedMoment B raw41687step2 raw41687step2Labels := by
      have ha : raw41687step2 = (fun i j => raw41687step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41687step2 raw41687step1; decide +kernel
      have hl : raw41687step2Labels = raw41687step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41687step1 raw41687step1Labels permutation17 permutation6
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw41688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41688Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41688step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41688step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41688step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41688step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41688step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41688step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41688 raw41688Labels = mixedMoment B node2779 node2779Labels := by
  calc
    mixedMoment B raw41688 raw41688Labels = mixedMoment B raw41688step0 raw41688step0Labels := by
      have hz : ∀ j, raw41688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41688step0 = (fun i j => raw41688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41688step0 raw41688; decide +kernel
      have hl : raw41688step0Labels = raw41688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41688 raw41688Labels permutation346 hz
    mixedMoment B raw41688step0 raw41688step0Labels = mixedMoment B raw41688step1 raw41688step1Labels := by
      have hz : ∀ j, raw41688step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41688step1 = (fun i j => raw41688step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41688step1 raw41688step0; decide +kernel
      have hl : raw41688step1Labels = raw41688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41688step0 raw41688step0Labels permutation56 hz
    mixedMoment B raw41688step1 raw41688step1Labels = mixedMoment B raw41688step2 raw41688step2Labels := by
      have ha : raw41688step2 = (fun i j => raw41688step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41688step2 raw41688step1; decide +kernel
      have hl : raw41688step2Labels = raw41688step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41688step1 raw41688step1Labels permutation12 permutation2
    mixedMoment B raw41688step2 raw41688step2Labels = mixedMoment B raw41688step3 raw41688step3Labels := by
      have ha : raw41688step3 = raw41688step2 := by apply Matrix.ext; unfold raw41688step3 raw41688step2; decide +kernel
      have hl : raw41688step2Labels = labelEmbedding1 ∘ raw41688step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41688step2 raw41688step2Labels raw41688step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2779 node2779Labels := by rfl

def raw41689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41689Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41689step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41689step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41689step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41689step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41689step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41689 raw41689Labels = mixedMoment B node5303 node5303Labels := by
  calc
    mixedMoment B raw41689 raw41689Labels = mixedMoment B raw41689step0 raw41689step0Labels := by
      have hz : ∀ j, raw41689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41689step0 = (fun i j => raw41689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41689step0 raw41689; decide +kernel
      have hl : raw41689step0Labels = raw41689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41689 raw41689Labels permutation346 hz
    mixedMoment B raw41689step0 raw41689step0Labels = mixedMoment B raw41689step1 raw41689step1Labels := by
      have hz : ∀ j, raw41689step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41689step1 = (fun i j => raw41689step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41689step1 raw41689step0; decide +kernel
      have hl : raw41689step1Labels = raw41689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41689step0 raw41689step0Labels permutation56 hz
    mixedMoment B raw41689step1 raw41689step1Labels = mixedMoment B raw41689step2 raw41689step2Labels := by
      have ha : raw41689step2 = (fun i j => raw41689step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41689step2 raw41689step1; decide +kernel
      have hl : raw41689step2Labels = raw41689step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41689step1 raw41689step1Labels permutation12 permutation2
    mixedMoment B raw41689step2 raw41689step2Labels = mixedMoment B raw41689step3 raw41689step3Labels := by
      have ha : raw41689step3 = raw41689step2 := by apply Matrix.ext; unfold raw41689step3 raw41689step2; decide +kernel
      have hl : raw41689step2Labels = labelEmbedding8 ∘ raw41689step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41689step2 raw41689step2Labels raw41689step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5303 node5303Labels := by rfl

def raw41690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41690Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41690step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41690 raw41690Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw41690 raw41690Labels = mixedMoment B raw41690step0 raw41690step0Labels := by
      have hz : ∀ j, raw41690 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41690step0 = (fun i j => raw41690 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41690step0 raw41690; decide +kernel
      have hl : raw41690step0Labels = raw41690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41690 raw41690Labels permutation265 hz
    mixedMoment B raw41690step0 raw41690step0Labels = mixedMoment B raw41690step1 raw41690step1Labels := by
      have ha : raw41690step1 = raw41690step0 := by apply Matrix.ext; unfold raw41690step1 raw41690step0; decide +kernel
      have hl : raw41690step0Labels = labelEmbedding1 ∘ raw41690step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41690step0 raw41690step0Labels raw41690step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw41691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41691Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41691step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41691step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41691 raw41691Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw41691 raw41691Labels = mixedMoment B raw41691step0 raw41691step0Labels := by
      have hz : ∀ j, raw41691 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41691step0 = (fun i j => raw41691 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41691step0 raw41691; decide +kernel
      have hl : raw41691step0Labels = raw41691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41691 raw41691Labels permutation265 hz
    mixedMoment B raw41691step0 raw41691step0Labels = mixedMoment B raw41691step1 raw41691step1Labels := by
      have ha : raw41691step1 = (fun i j => raw41691step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41691step1 raw41691step0; decide +kernel
      have hl : raw41691step1Labels = raw41691step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41691step0 raw41691step0Labels permutation149 permutation7
    mixedMoment B raw41691step1 raw41691step1Labels = mixedMoment B raw41691step2 raw41691step2Labels := by
      have ha : raw41691step2 = raw41691step1 := by apply Matrix.ext; unfold raw41691step2 raw41691step1; decide +kernel
      have hl : raw41691step1Labels = labelEmbedding6 ∘ raw41691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41691step1 raw41691step1Labels raw41691step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw41692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41692Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41692step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41692step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41692 raw41692Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw41692 raw41692Labels = mixedMoment B raw41692step0 raw41692step0Labels := by
      have hz : ∀ j, raw41692 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41692step0 = (fun i j => raw41692 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41692step0 raw41692; decide +kernel
      have hl : raw41692step0Labels = raw41692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41692 raw41692Labels permutation265 hz
    mixedMoment B raw41692step0 raw41692step0Labels = mixedMoment B raw41692step1 raw41692step1Labels := by
      have ha : raw41692step1 = (fun i j => raw41692step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41692step1 raw41692step0; decide +kernel
      have hl : raw41692step1Labels = raw41692step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41692step0 raw41692step0Labels permutation37 permutation2
    mixedMoment B raw41692step1 raw41692step1Labels = mixedMoment B raw41692step2 raw41692step2Labels := by
      have ha : raw41692step2 = raw41692step1 := by apply Matrix.ext; unfold raw41692step2 raw41692step1; decide +kernel
      have hl : raw41692step1Labels = labelEmbedding1 ∘ raw41692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41692step1 raw41692step1Labels raw41692step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw41693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41693Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41693step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41693 raw41693Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw41693 raw41693Labels = mixedMoment B raw41693step0 raw41693step0Labels := by
      have hz : ∀ j, raw41693 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41693step0 = (fun i j => raw41693 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41693step0 raw41693; decide +kernel
      have hl : raw41693step0Labels = raw41693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41693 raw41693Labels permutation265 hz
    mixedMoment B raw41693step0 raw41693step0Labels = mixedMoment B raw41693step1 raw41693step1Labels := by
      have ha : raw41693step1 = (fun i j => raw41693step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41693step1 raw41693step0; decide +kernel
      have hl : raw41693step1Labels = raw41693step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41693step0 raw41693step0Labels permutation95 permutation6
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw41694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41694Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41694step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41694 raw41694Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw41694 raw41694Labels = mixedMoment B raw41694step0 raw41694step0Labels := by
      have hz : ∀ j, raw41694 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41694step0 = (fun i j => raw41694 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41694step0 raw41694; decide +kernel
      have hl : raw41694step0Labels = raw41694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41694 raw41694Labels permutation265 hz
    mixedMoment B raw41694step0 raw41694step0Labels = mixedMoment B raw41694step1 raw41694step1Labels := by
      have ha : raw41694step1 = (fun i j => raw41694step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41694step1 raw41694step0; decide +kernel
      have hl : raw41694step1Labels = raw41694step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41694step0 raw41694step0Labels permutation35 permutation2
    mixedMoment B raw41694step1 raw41694step1Labels = mixedMoment B raw41694step2 raw41694step2Labels := by
      have ha : raw41694step2 = raw41694step1 := by apply Matrix.ext; unfold raw41694step2 raw41694step1; decide +kernel
      have hl : raw41694step1Labels = labelEmbedding1 ∘ raw41694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41694step1 raw41694step1Labels raw41694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw41695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41695Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41695step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41695step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41695 raw41695Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw41695 raw41695Labels = mixedMoment B raw41695step0 raw41695step0Labels := by
      have hz : ∀ j, raw41695 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41695step0 = (fun i j => raw41695 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41695step0 raw41695; decide +kernel
      have hl : raw41695step0Labels = raw41695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41695 raw41695Labels permutation265 hz
    mixedMoment B raw41695step0 raw41695step0Labels = mixedMoment B raw41695step1 raw41695step1Labels := by
      have ha : raw41695step1 = (fun i j => raw41695step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41695step1 raw41695step0; decide +kernel
      have hl : raw41695step1Labels = raw41695step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41695step0 raw41695step0Labels permutation35 permutation2
    mixedMoment B raw41695step1 raw41695step1Labels = mixedMoment B raw41695step2 raw41695step2Labels := by
      have ha : raw41695step2 = raw41695step1 := by apply Matrix.ext; unfold raw41695step2 raw41695step1; decide +kernel
      have hl : raw41695step1Labels = labelEmbedding8 ∘ raw41695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41695step1 raw41695step1Labels raw41695step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw41696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41696Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41696step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41696step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41696 raw41696Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw41696 raw41696Labels = mixedMoment B raw41696step0 raw41696step0Labels := by
      have hz : ∀ j, raw41696 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41696step0 = (fun i j => raw41696 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41696step0 raw41696; decide +kernel
      have hl : raw41696step0Labels = raw41696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41696 raw41696Labels permutation265 hz
    mixedMoment B raw41696step0 raw41696step0Labels = mixedMoment B raw41696step1 raw41696step1Labels := by
      have ha : raw41696step1 = (fun i j => raw41696step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41696step1 raw41696step0; decide +kernel
      have hl : raw41696step1Labels = raw41696step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41696step0 raw41696step0Labels permutation36 permutation2
    mixedMoment B raw41696step1 raw41696step1Labels = mixedMoment B raw41696step2 raw41696step2Labels := by
      have ha : raw41696step2 = raw41696step1 := by apply Matrix.ext; unfold raw41696step2 raw41696step1; decide +kernel
      have hl : raw41696step1Labels = labelEmbedding1 ∘ raw41696step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41696step1 raw41696step1Labels raw41696step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw41697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41697Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41697step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41697step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41697 raw41697Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw41697 raw41697Labels = mixedMoment B raw41697step0 raw41697step0Labels := by
      have hz : ∀ j, raw41697 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41697step0 = (fun i j => raw41697 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41697step0 raw41697; decide +kernel
      have hl : raw41697step0Labels = raw41697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41697 raw41697Labels permutation265 hz
    mixedMoment B raw41697step0 raw41697step0Labels = mixedMoment B raw41697step1 raw41697step1Labels := by
      have ha : raw41697step1 = (fun i j => raw41697step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41697step1 raw41697step0; decide +kernel
      have hl : raw41697step1Labels = raw41697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41697step0 raw41697step0Labels permutation36 permutation2
    mixedMoment B raw41697step1 raw41697step1Labels = mixedMoment B raw41697step2 raw41697step2Labels := by
      have ha : raw41697step2 = raw41697step1 := by apply Matrix.ext; unfold raw41697step2 raw41697step1; decide +kernel
      have hl : raw41697step1Labels = labelEmbedding8 ∘ raw41697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41697step1 raw41697step1Labels raw41697step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw41698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41698Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41698step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41698 raw41698Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw41698 raw41698Labels = mixedMoment B raw41698step0 raw41698step0Labels := by
      have hz : ∀ j, raw41698 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41698step0 = (fun i j => raw41698 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41698step0 raw41698; decide +kernel
      have hl : raw41698step0Labels = raw41698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41698 raw41698Labels permutation265 hz
    mixedMoment B raw41698step0 raw41698step0Labels = mixedMoment B raw41698step1 raw41698step1Labels := by
      have ha : raw41698step1 = (fun i j => raw41698step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41698step1 raw41698step0; decide +kernel
      have hl : raw41698step1Labels = raw41698step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41698step0 raw41698step0Labels permutation37 permutation2
    mixedMoment B raw41698step1 raw41698step1Labels = mixedMoment B raw41698step2 raw41698step2Labels := by
      have ha : raw41698step2 = raw41698step1 := by apply Matrix.ext; unfold raw41698step2 raw41698step1; decide +kernel
      have hl : raw41698step1Labels = labelEmbedding1 ∘ raw41698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41698step1 raw41698step1Labels raw41698step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw41699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41699Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41699step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41699 raw41699Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw41699 raw41699Labels = mixedMoment B raw41699step0 raw41699step0Labels := by
      have hz : ∀ j, raw41699 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41699step0 = (fun i j => raw41699 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41699step0 raw41699; decide +kernel
      have hl : raw41699step0Labels = raw41699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41699 raw41699Labels permutation265 hz
    mixedMoment B raw41699step0 raw41699step0Labels = mixedMoment B raw41699step1 raw41699step1Labels := by
      have ha : raw41699step1 = (fun i j => raw41699step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41699step1 raw41699step0; decide +kernel
      have hl : raw41699step1Labels = raw41699step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41699step0 raw41699step0Labels permutation96 permutation6
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw41700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41700Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41700step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41700 raw41700Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw41700 raw41700Labels = mixedMoment B raw41700step0 raw41700step0Labels := by
      have hz : ∀ j, raw41700 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41700step0 = (fun i j => raw41700 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41700step0 raw41700; decide +kernel
      have hl : raw41700step0Labels = raw41700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41700 raw41700Labels permutation265 hz
    mixedMoment B raw41700step0 raw41700step0Labels = mixedMoment B raw41700step1 raw41700step1Labels := by
      have ha : raw41700step1 = (fun i j => raw41700step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41700step1 raw41700step0; decide +kernel
      have hl : raw41700step1Labels = raw41700step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41700step0 raw41700step0Labels permutation36 permutation2
    mixedMoment B raw41700step1 raw41700step1Labels = mixedMoment B raw41700step2 raw41700step2Labels := by
      have ha : raw41700step2 = raw41700step1 := by apply Matrix.ext; unfold raw41700step2 raw41700step1; decide +kernel
      have hl : raw41700step1Labels = labelEmbedding1 ∘ raw41700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41700step1 raw41700step1Labels raw41700step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw41701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41701Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41701step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41701step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41701step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41701 raw41701Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw41701 raw41701Labels = mixedMoment B raw41701step0 raw41701step0Labels := by
      have hz : ∀ j, raw41701 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41701step0 = (fun i j => raw41701 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41701step0 raw41701; decide +kernel
      have hl : raw41701step0Labels = raw41701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41701 raw41701Labels permutation265 hz
    mixedMoment B raw41701step0 raw41701step0Labels = mixedMoment B raw41701step1 raw41701step1Labels := by
      have ha : raw41701step1 = (fun i j => raw41701step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41701step1 raw41701step0; decide +kernel
      have hl : raw41701step1Labels = raw41701step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41701step0 raw41701step0Labels permutation36 permutation2
    mixedMoment B raw41701step1 raw41701step1Labels = mixedMoment B raw41701step2 raw41701step2Labels := by
      have ha : raw41701step2 = raw41701step1 := by apply Matrix.ext; unfold raw41701step2 raw41701step1; decide +kernel
      have hl : raw41701step1Labels = labelEmbedding8 ∘ raw41701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41701step1 raw41701step1Labels raw41701step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw41702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41702Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41702step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41702 raw41702Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw41702 raw41702Labels = mixedMoment B raw41702step0 raw41702step0Labels := by
      have ha : raw41702step0 = (fun i j => raw41702 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41702step0 raw41702; decide +kernel
      have hl : raw41702step0Labels = raw41702Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41702 raw41702Labels permutation157 permutation2
    mixedMoment B raw41702step0 raw41702step0Labels = mixedMoment B raw41702step1 raw41702step1Labels := by
      have ha : raw41702step1 = raw41702step0 := by apply Matrix.ext; unfold raw41702step1 raw41702step0; decide +kernel
      have hl : raw41702step0Labels = labelEmbedding1 ∘ raw41702step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41702step0 raw41702step0Labels raw41702step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw41703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41703Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41703 raw41703Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw41703 raw41703Labels = mixedMoment B raw41703step0 raw41703step0Labels := by
      have ha : raw41703step0 = (fun i j => raw41703 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41703step0 raw41703; decide +kernel
      have hl : raw41703step0Labels = raw41703Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41703 raw41703Labels permutation502 permutation6
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw41704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41704Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw41704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41704step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw41704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41704step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw41704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41704 raw41704Labels = mixedMoment B node2285 node2285Labels := by
  calc
    mixedMoment B raw41704 raw41704Labels = mixedMoment B raw41704step0 raw41704step0Labels := by
      have hz : ∀ j, raw41704 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41704step0 = (fun i j => raw41704 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41704step0 raw41704; decide +kernel
      have hl : raw41704step0Labels = raw41704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41704 raw41704Labels permutation520 hz
    mixedMoment B raw41704step0 raw41704step0Labels = mixedMoment B raw41704step1 raw41704step1Labels := by
      have hz : ∀ j, raw41704step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41704step1 = (fun i j => raw41704step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41704step1 raw41704step0; decide +kernel
      have hl : raw41704step1Labels = raw41704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41704step0 raw41704step0Labels permutation104 hz
    mixedMoment B raw41704step1 raw41704step1Labels = mixedMoment B raw41704step2 raw41704step2Labels := by
      have hz : ∀ j, raw41704step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41704step2 = (fun i j => raw41704step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41704step2 raw41704step1; decide +kernel
      have hl : raw41704step2Labels = raw41704step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41704step1 raw41704step1Labels permutation20 hz
    mixedMoment B raw41704step2 raw41704step2Labels = mixedMoment B raw41704step3 raw41704step3Labels := by
      have ha : raw41704step3 = raw41704step2 := by apply Matrix.ext; unfold raw41704step3 raw41704step2; decide +kernel
      have hl : raw41704step2Labels = labelEmbedding1 ∘ raw41704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41704step2 raw41704step2Labels raw41704step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2285 node2285Labels := by rfl

def raw41705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41705Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41705step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw41705step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41705step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw41705step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41705step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw41705step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41705 raw41705Labels = mixedMoment B node4900 node4900Labels := by
  calc
    mixedMoment B raw41705 raw41705Labels = mixedMoment B raw41705step0 raw41705step0Labels := by
      have hz : ∀ j, raw41705 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41705step0 = (fun i j => raw41705 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41705step0 raw41705; decide +kernel
      have hl : raw41705step0Labels = raw41705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41705 raw41705Labels permutation520 hz
    mixedMoment B raw41705step0 raw41705step0Labels = mixedMoment B raw41705step1 raw41705step1Labels := by
      have hz : ∀ j, raw41705step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41705step1 = (fun i j => raw41705step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41705step1 raw41705step0; decide +kernel
      have hl : raw41705step1Labels = raw41705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41705step0 raw41705step0Labels permutation104 hz
    mixedMoment B raw41705step1 raw41705step1Labels = mixedMoment B raw41705step2 raw41705step2Labels := by
      have hz : ∀ j, raw41705step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41705step2 = (fun i j => raw41705step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41705step2 raw41705step1; decide +kernel
      have hl : raw41705step2Labels = raw41705step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41705step1 raw41705step1Labels permutation20 hz
    mixedMoment B raw41705step2 raw41705step2Labels = mixedMoment B raw41705step3 raw41705step3Labels := by
      have ha : raw41705step3 = raw41705step2 := by apply Matrix.ext; unfold raw41705step3 raw41705step2; decide +kernel
      have hl : raw41705step2Labels = labelEmbedding8 ∘ raw41705step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41705step2 raw41705step2Labels raw41705step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4900 node4900Labels := by rfl

def raw41706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41706Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41706step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw41706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw41706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw41706step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41706step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw41706step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41706 raw41706Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw41706 raw41706Labels = mixedMoment B raw41706step0 raw41706step0Labels := by
      have hz : ∀ j, raw41706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41706step0 = (fun i j => raw41706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41706step0 raw41706; decide +kernel
      have hl : raw41706step0Labels = raw41706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41706 raw41706Labels permutation434 hz
    mixedMoment B raw41706step0 raw41706step0Labels = mixedMoment B raw41706step1 raw41706step1Labels := by
      have hz : ∀ j, raw41706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41706step1 = (fun i j => raw41706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41706step1 raw41706step0; decide +kernel
      have hl : raw41706step1Labels = raw41706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41706step0 raw41706step0Labels permutation80 hz
    mixedMoment B raw41706step1 raw41706step1Labels = mixedMoment B raw41706step2 raw41706step2Labels := by
      have ha : raw41706step2 = (fun i j => raw41706step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41706step2 raw41706step1; decide +kernel
      have hl : raw41706step2Labels = raw41706step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41706step1 raw41706step1Labels permutation16 permutation4
    mixedMoment B raw41706step2 raw41706step2Labels = mixedMoment B raw41706step3 raw41706step3Labels := by
      have ha : raw41706step3 = -raw41706step2 := by apply Matrix.ext; change ∀ i j, raw41706step3 i j = -(raw41706step2 i j); unfold raw41706step3 raw41706step2; decide +kernel
      have hl : raw41706step3Labels = raw41706step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41706step3 raw41706step3Labels = mixedMoment B raw41706step4 raw41706step4Labels := by
      have ha : raw41706step4 = raw41706step3 := by apply Matrix.ext; unfold raw41706step4 raw41706step3; decide +kernel
      have hl : raw41706step3Labels = labelEmbedding1 ∘ raw41706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41706step3 raw41706step3Labels raw41706step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw41707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41707Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41707step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw41707step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw41707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41707 raw41707Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw41707 raw41707Labels = mixedMoment B raw41707step0 raw41707step0Labels := by
      have hz : ∀ j, raw41707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41707step0 = (fun i j => raw41707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41707step0 raw41707; decide +kernel
      have hl : raw41707step0Labels = raw41707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41707 raw41707Labels permutation434 hz
    mixedMoment B raw41707step0 raw41707step0Labels = mixedMoment B raw41707step1 raw41707step1Labels := by
      have hz : ∀ j, raw41707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41707step1 = (fun i j => raw41707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41707step1 raw41707step0; decide +kernel
      have hl : raw41707step1Labels = raw41707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41707step0 raw41707step0Labels permutation80 hz
    mixedMoment B raw41707step1 raw41707step1Labels = mixedMoment B raw41707step2 raw41707step2Labels := by
      have ha : raw41707step2 = (fun i j => raw41707step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41707step2 raw41707step1; decide +kernel
      have hl : raw41707step2Labels = raw41707step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41707step1 raw41707step1Labels permutation17 permutation6
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw41708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41708Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41708step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw41708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw41708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41708 raw41708Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw41708 raw41708Labels = mixedMoment B raw41708step0 raw41708step0Labels := by
      have hz : ∀ j, raw41708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41708step0 = (fun i j => raw41708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41708step0 raw41708; decide +kernel
      have hl : raw41708step0Labels = raw41708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41708 raw41708Labels permutation434 hz
    mixedMoment B raw41708step0 raw41708step0Labels = mixedMoment B raw41708step1 raw41708step1Labels := by
      have hz : ∀ j, raw41708step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41708step1 = (fun i j => raw41708step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41708step1 raw41708step0; decide +kernel
      have hl : raw41708step1Labels = raw41708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41708step0 raw41708step0Labels permutation80 hz
    mixedMoment B raw41708step1 raw41708step1Labels = mixedMoment B raw41708step2 raw41708step2Labels := by
      have ha : raw41708step2 = raw41708step1 := by apply Matrix.ext; unfold raw41708step2 raw41708step1; decide +kernel
      have hl : raw41708step1Labels = labelEmbedding1 ∘ raw41708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41708step1 raw41708step1Labels raw41708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2284 node2284Labels := by rfl

def raw41709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41709Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41709step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw41709step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw41709step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41709 raw41709Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw41709 raw41709Labels = mixedMoment B raw41709step0 raw41709step0Labels := by
      have hz : ∀ j, raw41709 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41709step0 = (fun i j => raw41709 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41709step0 raw41709; decide +kernel
      have hl : raw41709step0Labels = raw41709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41709 raw41709Labels permutation434 hz
    mixedMoment B raw41709step0 raw41709step0Labels = mixedMoment B raw41709step1 raw41709step1Labels := by
      have hz : ∀ j, raw41709step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41709step1 = (fun i j => raw41709step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41709step1 raw41709step0; decide +kernel
      have hl : raw41709step1Labels = raw41709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41709step0 raw41709step0Labels permutation80 hz
    mixedMoment B raw41709step1 raw41709step1Labels = mixedMoment B raw41709step2 raw41709step2Labels := by
      have ha : raw41709step2 = (fun i j => raw41709step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41709step2 raw41709step1; decide +kernel
      have hl : raw41709step2Labels = raw41709step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41709step1 raw41709step1Labels permutation17 permutation6
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw41710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41710Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41710step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw41710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw41710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41710 raw41710Labels = mixedMoment B node2282 node2282Labels := by
  calc
    mixedMoment B raw41710 raw41710Labels = mixedMoment B raw41710step0 raw41710step0Labels := by
      have hz : ∀ j, raw41710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41710step0 = (fun i j => raw41710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41710step0 raw41710; decide +kernel
      have hl : raw41710step0Labels = raw41710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41710 raw41710Labels permutation434 hz
    mixedMoment B raw41710step0 raw41710step0Labels = mixedMoment B raw41710step1 raw41710step1Labels := by
      have hz : ∀ j, raw41710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41710step1 = (fun i j => raw41710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41710step1 raw41710step0; decide +kernel
      have hl : raw41710step1Labels = raw41710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41710step0 raw41710step0Labels permutation80 hz
    mixedMoment B raw41710step1 raw41710step1Labels = mixedMoment B raw41710step2 raw41710step2Labels := by
      have ha : raw41710step2 = raw41710step1 := by apply Matrix.ext; unfold raw41710step2 raw41710step1; decide +kernel
      have hl : raw41710step1Labels = labelEmbedding1 ∘ raw41710step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41710step1 raw41710step1Labels raw41710step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2282 node2282Labels := by rfl

def raw41711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41711Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41711step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw41711step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41711step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41711 raw41711Labels = mixedMoment B node4872 node4872Labels := by
  calc
    mixedMoment B raw41711 raw41711Labels = mixedMoment B raw41711step0 raw41711step0Labels := by
      have hz : ∀ j, raw41711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41711step0 = (fun i j => raw41711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41711step0 raw41711; decide +kernel
      have hl : raw41711step0Labels = raw41711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41711 raw41711Labels permutation434 hz
    mixedMoment B raw41711step0 raw41711step0Labels = mixedMoment B raw41711step1 raw41711step1Labels := by
      have hz : ∀ j, raw41711step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41711step1 = (fun i j => raw41711step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41711step1 raw41711step0; decide +kernel
      have hl : raw41711step1Labels = raw41711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41711step0 raw41711step0Labels permutation80 hz
    mixedMoment B raw41711step1 raw41711step1Labels = mixedMoment B raw41711step2 raw41711step2Labels := by
      have ha : raw41711step2 = (fun i j => raw41711step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41711step2 raw41711step1; decide +kernel
      have hl : raw41711step2Labels = raw41711step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41711step1 raw41711step1Labels permutation19 permutation6
    _ = mixedMoment B node4872 node4872Labels := by rfl

def raw41712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41712Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41712step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw41712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-3, 1, 2]]
def raw41712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw41712step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41712step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw41712step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41712 raw41712Labels = mixedMoment B node2163 node2163Labels := by
  calc
    mixedMoment B raw41712 raw41712Labels = mixedMoment B raw41712step0 raw41712step0Labels := by
      have hz : ∀ j, raw41712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41712step0 = (fun i j => raw41712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41712step0 raw41712; decide +kernel
      have hl : raw41712step0Labels = raw41712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41712 raw41712Labels permutation434 hz
    mixedMoment B raw41712step0 raw41712step0Labels = mixedMoment B raw41712step1 raw41712step1Labels := by
      have hz : ∀ j, raw41712step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41712step1 = (fun i j => raw41712step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41712step1 raw41712step0; decide +kernel
      have hl : raw41712step1Labels = raw41712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41712step0 raw41712step0Labels permutation80 hz
    mixedMoment B raw41712step1 raw41712step1Labels = mixedMoment B raw41712step2 raw41712step2Labels := by
      have ha : raw41712step2 = (fun i j => raw41712step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41712step2 raw41712step1; decide +kernel
      have hl : raw41712step2Labels = raw41712step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41712step1 raw41712step1Labels permutation18 permutation4
    mixedMoment B raw41712step2 raw41712step2Labels = mixedMoment B raw41712step3 raw41712step3Labels := by
      have ha : raw41712step3 = -raw41712step2 := by apply Matrix.ext; change ∀ i j, raw41712step3 i j = -(raw41712step2 i j); unfold raw41712step3 raw41712step2; decide +kernel
      have hl : raw41712step3Labels = raw41712step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41712step3 raw41712step3Labels = mixedMoment B raw41712step4 raw41712step4Labels := by
      have ha : raw41712step4 = raw41712step3 := by apply Matrix.ext; unfold raw41712step4 raw41712step3; decide +kernel
      have hl : raw41712step3Labels = labelEmbedding1 ∘ raw41712step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41712step3 raw41712step3Labels raw41712step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2163 node2163Labels := by rfl

def raw41713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41713Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41713step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw41713step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw41713step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41713 raw41713Labels = mixedMoment B node4694 node4694Labels := by
  calc
    mixedMoment B raw41713 raw41713Labels = mixedMoment B raw41713step0 raw41713step0Labels := by
      have hz : ∀ j, raw41713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41713step0 = (fun i j => raw41713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41713step0 raw41713; decide +kernel
      have hl : raw41713step0Labels = raw41713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41713 raw41713Labels permutation434 hz
    mixedMoment B raw41713step0 raw41713step0Labels = mixedMoment B raw41713step1 raw41713step1Labels := by
      have hz : ∀ j, raw41713step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41713step1 = (fun i j => raw41713step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41713step1 raw41713step0; decide +kernel
      have hl : raw41713step1Labels = raw41713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41713step0 raw41713step0Labels permutation80 hz
    mixedMoment B raw41713step1 raw41713step1Labels = mixedMoment B raw41713step2 raw41713step2Labels := by
      have ha : raw41713step2 = (fun i j => raw41713step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41713step2 raw41713step1; decide +kernel
      have hl : raw41713step2Labels = raw41713step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41713step1 raw41713step1Labels permutation19 permutation6
    _ = mixedMoment B node4694 node4694Labels := by rfl

def raw41714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41714Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41714step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41714 raw41714Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw41714 raw41714Labels = mixedMoment B raw41714step0 raw41714step0Labels := by
      have hz : ∀ j, raw41714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41714step0 = (fun i j => raw41714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41714step0 raw41714; decide +kernel
      have hl : raw41714step0Labels = raw41714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41714 raw41714Labels permutation346 hz
    mixedMoment B raw41714step0 raw41714step0Labels = mixedMoment B raw41714step1 raw41714step1Labels := by
      have ha : raw41714step1 = (fun i j => raw41714step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41714step1 raw41714step0; decide +kernel
      have hl : raw41714step1Labels = raw41714step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41714step0 raw41714step0Labels permutation38 permutation2
    mixedMoment B raw41714step1 raw41714step1Labels = mixedMoment B raw41714step2 raw41714step2Labels := by
      have ha : raw41714step2 = raw41714step1 := by apply Matrix.ext; unfold raw41714step2 raw41714step1; decide +kernel
      have hl : raw41714step1Labels = labelEmbedding1 ∘ raw41714step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41714step1 raw41714step1Labels raw41714step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2221 node2221Labels := by rfl

def raw41715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41715Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41715step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw41715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41715 raw41715Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw41715 raw41715Labels = mixedMoment B raw41715step0 raw41715step0Labels := by
      have hz : ∀ j, raw41715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41715step0 = (fun i j => raw41715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41715step0 raw41715; decide +kernel
      have hl : raw41715step0Labels = raw41715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41715 raw41715Labels permutation346 hz
    mixedMoment B raw41715step0 raw41715step0Labels = mixedMoment B raw41715step1 raw41715step1Labels := by
      have ha : raw41715step1 = (fun i j => raw41715step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41715step1 raw41715step0; decide +kernel
      have hl : raw41715step1Labels = raw41715step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41715step0 raw41715step0Labels permutation73 permutation6
    _ = mixedMoment B node4819 node4819Labels := by rfl

def raw41716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41716Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41716 raw41716Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw41716 raw41716Labels = mixedMoment B raw41716step0 raw41716step0Labels := by
      have hz : ∀ j, raw41716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41716step0 = (fun i j => raw41716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41716step0 raw41716; decide +kernel
      have hl : raw41716step0Labels = raw41716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41716 raw41716Labels permutation346 hz
    mixedMoment B raw41716step0 raw41716step0Labels = mixedMoment B raw41716step1 raw41716step1Labels := by
      have ha : raw41716step1 = (fun i j => raw41716step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41716step1 raw41716step0; decide +kernel
      have hl : raw41716step1Labels = raw41716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41716step0 raw41716step0Labels permutation38 permutation2
    mixedMoment B raw41716step1 raw41716step1Labels = mixedMoment B raw41716step2 raw41716step2Labels := by
      have ha : raw41716step2 = raw41716step1 := by apply Matrix.ext; unfold raw41716step2 raw41716step1; decide +kernel
      have hl : raw41716step1Labels = labelEmbedding1 ∘ raw41716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41716step1 raw41716step1Labels raw41716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw41717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41717Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41717step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw41717step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41717step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41717step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41717step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41717 raw41717Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw41717 raw41717Labels = mixedMoment B raw41717step0 raw41717step0Labels := by
      have hz : ∀ j, raw41717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41717step0 = (fun i j => raw41717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41717step0 raw41717; decide +kernel
      have hl : raw41717step0Labels = raw41717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41717 raw41717Labels permutation346 hz
    mixedMoment B raw41717step0 raw41717step0Labels = mixedMoment B raw41717step1 raw41717step1Labels := by
      have ha : raw41717step1 = (fun i j => raw41717step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41717step1 raw41717step0; decide +kernel
      have hl : raw41717step1Labels = raw41717step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41717step0 raw41717step0Labels permutation41 permutation7
    mixedMoment B raw41717step1 raw41717step1Labels = mixedMoment B raw41717step2 raw41717step2Labels := by
      have ha : raw41717step2 = -raw41717step1 := by apply Matrix.ext; change ∀ i j, raw41717step2 i j = -(raw41717step1 i j); unfold raw41717step2 raw41717step1; decide +kernel
      have hl : raw41717step2Labels = raw41717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41717step2 raw41717step2Labels = mixedMoment B raw41717step3 raw41717step3Labels := by
      have ha : raw41717step3 = raw41717step2 := by apply Matrix.ext; unfold raw41717step3 raw41717step2; decide +kernel
      have hl : raw41717step2Labels = labelEmbedding6 ∘ raw41717step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41717step2 raw41717step2Labels raw41717step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw41718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41718Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw41718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41718 raw41718Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw41718 raw41718Labels = mixedMoment B raw41718step0 raw41718step0Labels := by
      have hz : ∀ j, raw41718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41718step0 = (fun i j => raw41718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41718step0 raw41718; decide +kernel
      have hl : raw41718step0Labels = raw41718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41718 raw41718Labels permutation346 hz
    mixedMoment B raw41718step0 raw41718step0Labels = mixedMoment B raw41718step1 raw41718step1Labels := by
      have ha : raw41718step1 = (fun i j => raw41718step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41718step1 raw41718step0; decide +kernel
      have hl : raw41718step1Labels = raw41718step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41718step0 raw41718step0Labels permutation74 permutation4
    mixedMoment B raw41718step1 raw41718step1Labels = mixedMoment B raw41718step2 raw41718step2Labels := by
      have ha : raw41718step2 = -raw41718step1 := by apply Matrix.ext; change ∀ i j, raw41718step2 i j = -(raw41718step1 i j); unfold raw41718step2 raw41718step1; decide +kernel
      have hl : raw41718step2Labels = raw41718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41718step2 raw41718step2Labels = mixedMoment B raw41718step3 raw41718step3Labels := by
      have ha : raw41718step3 = raw41718step2 := by apply Matrix.ext; unfold raw41718step3 raw41718step2; decide +kernel
      have hl : raw41718step2Labels = labelEmbedding1 ∘ raw41718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41718step2 raw41718step2Labels raw41718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2162 node2162Labels := by rfl

def raw41719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41719Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41719step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41719 raw41719Labels = mixedMoment B node4687 node4687Labels := by
  calc
    mixedMoment B raw41719 raw41719Labels = mixedMoment B raw41719step0 raw41719step0Labels := by
      have hz : ∀ j, raw41719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41719step0 = (fun i j => raw41719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41719step0 raw41719; decide +kernel
      have hl : raw41719step0Labels = raw41719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41719 raw41719Labels permutation346 hz
    mixedMoment B raw41719step0 raw41719step0Labels = mixedMoment B raw41719step1 raw41719step1Labels := by
      have ha : raw41719step1 = (fun i j => raw41719step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41719step1 raw41719step0; decide +kernel
      have hl : raw41719step1Labels = raw41719step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41719step0 raw41719step0Labels permutation77 permutation6
    _ = mixedMoment B node4687 node4687Labels := by rfl

def raw41720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41720Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41720step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41720 raw41720Labels = mixedMoment B node2161 node2161Labels := by
  calc
    mixedMoment B raw41720 raw41720Labels = mixedMoment B raw41720step0 raw41720step0Labels := by
      have hz : ∀ j, raw41720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41720step0 = (fun i j => raw41720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41720step0 raw41720; decide +kernel
      have hl : raw41720step0Labels = raw41720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41720 raw41720Labels permutation346 hz
    mixedMoment B raw41720step0 raw41720step0Labels = mixedMoment B raw41720step1 raw41720step1Labels := by
      have ha : raw41720step1 = (fun i j => raw41720step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41720step1 raw41720step0; decide +kernel
      have hl : raw41720step1Labels = raw41720step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41720step0 raw41720step0Labels permutation38 permutation2
    mixedMoment B raw41720step1 raw41720step1Labels = mixedMoment B raw41720step2 raw41720step2Labels := by
      have ha : raw41720step2 = raw41720step1 := by apply Matrix.ext; unfold raw41720step2 raw41720step1; decide +kernel
      have hl : raw41720step1Labels = labelEmbedding1 ∘ raw41720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41720step1 raw41720step1Labels raw41720step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2161 node2161Labels := by rfl

def raw41721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41721Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41721step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41721 raw41721Labels = mixedMoment B node4671 node4671Labels := by
  calc
    mixedMoment B raw41721 raw41721Labels = mixedMoment B raw41721step0 raw41721step0Labels := by
      have hz : ∀ j, raw41721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41721step0 = (fun i j => raw41721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41721step0 raw41721; decide +kernel
      have hl : raw41721step0Labels = raw41721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41721 raw41721Labels permutation346 hz
    mixedMoment B raw41721step0 raw41721step0Labels = mixedMoment B raw41721step1 raw41721step1Labels := by
      have ha : raw41721step1 = (fun i j => raw41721step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41721step1 raw41721step0; decide +kernel
      have hl : raw41721step1Labels = raw41721step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41721step0 raw41721step0Labels permutation79 permutation6
    _ = mixedMoment B node4671 node4671Labels := by rfl

def raw41722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41722Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw41722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw41722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41722step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw41722step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41722 raw41722Labels = mixedMoment B node2180 node2180Labels := by
  calc
    mixedMoment B raw41722 raw41722Labels = mixedMoment B raw41722step0 raw41722step0Labels := by
      have hz : ∀ j, raw41722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41722step0 = (fun i j => raw41722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41722step0 raw41722; decide +kernel
      have hl : raw41722step0Labels = raw41722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41722 raw41722Labels permutation346 hz
    mixedMoment B raw41722step0 raw41722step0Labels = mixedMoment B raw41722step1 raw41722step1Labels := by
      have ha : raw41722step1 = (fun i j => raw41722step0 (permutation64 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41722step1 raw41722step0; decide +kernel
      have hl : raw41722step1Labels = raw41722step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41722step0 raw41722step0Labels permutation64 permutation4
    mixedMoment B raw41722step1 raw41722step1Labels = mixedMoment B raw41722step2 raw41722step2Labels := by
      have ha : raw41722step2 = -raw41722step1 := by apply Matrix.ext; change ∀ i j, raw41722step2 i j = -(raw41722step1 i j); unfold raw41722step2 raw41722step1; decide +kernel
      have hl : raw41722step2Labels = raw41722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41722step2 raw41722step2Labels = mixedMoment B raw41722step3 raw41722step3Labels := by
      have ha : raw41722step3 = raw41722step2 := by apply Matrix.ext; unfold raw41722step3 raw41722step2; decide +kernel
      have hl : raw41722step2Labels = labelEmbedding1 ∘ raw41722step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41722step2 raw41722step2Labels raw41722step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2180 node2180Labels := by rfl

def raw41723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41723Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41723step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41723step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41723step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41723step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41723 raw41723Labels = mixedMoment B node4702 node4702Labels := by
  calc
    mixedMoment B raw41723 raw41723Labels = mixedMoment B raw41723step0 raw41723step0Labels := by
      have hz : ∀ j, raw41723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41723step0 = (fun i j => raw41723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41723step0 raw41723; decide +kernel
      have hl : raw41723step0Labels = raw41723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41723 raw41723Labels permutation346 hz
    mixedMoment B raw41723step0 raw41723step0Labels = mixedMoment B raw41723step1 raw41723step1Labels := by
      have ha : raw41723step1 = (fun i j => raw41723step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41723step1 raw41723step0; decide +kernel
      have hl : raw41723step1Labels = raw41723step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41723step0 raw41723step0Labels permutation53 permutation7
    mixedMoment B raw41723step1 raw41723step1Labels = mixedMoment B raw41723step2 raw41723step2Labels := by
      have ha : raw41723step2 = -raw41723step1 := by apply Matrix.ext; change ∀ i j, raw41723step2 i j = -(raw41723step1 i j); unfold raw41723step2 raw41723step1; decide +kernel
      have hl : raw41723step2Labels = raw41723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41723step2 raw41723step2Labels = mixedMoment B raw41723step3 raw41723step3Labels := by
      have ha : raw41723step3 = raw41723step2 := by apply Matrix.ext; unfold raw41723step3 raw41723step2; decide +kernel
      have hl : raw41723step2Labels = labelEmbedding6 ∘ raw41723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41723step2 raw41723step2Labels raw41723step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4702 node4702Labels := by rfl

def raw41724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41724Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41724step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw41724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41724 raw41724Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw41724 raw41724Labels = mixedMoment B raw41724step0 raw41724step0Labels := by
      have hz : ∀ j, raw41724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41724step0 = (fun i j => raw41724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41724step0 raw41724; decide +kernel
      have hl : raw41724step0Labels = raw41724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41724 raw41724Labels permutation346 hz
    mixedMoment B raw41724step0 raw41724step0Labels = mixedMoment B raw41724step1 raw41724step1Labels := by
      have ha : raw41724step1 = (fun i j => raw41724step0 (permutation62 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41724step1 raw41724step0; decide +kernel
      have hl : raw41724step1Labels = raw41724step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41724step0 raw41724step0Labels permutation62 permutation4
    mixedMoment B raw41724step1 raw41724step1Labels = mixedMoment B raw41724step2 raw41724step2Labels := by
      have ha : raw41724step2 = -raw41724step1 := by apply Matrix.ext; change ∀ i j, raw41724step2 i j = -(raw41724step1 i j); unfold raw41724step2 raw41724step1; decide +kernel
      have hl : raw41724step2Labels = raw41724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41724step2 raw41724step2Labels = mixedMoment B raw41724step3 raw41724step3Labels := by
      have ha : raw41724step3 = raw41724step2 := by apply Matrix.ext; unfold raw41724step3 raw41724step2; decide +kernel
      have hl : raw41724step2Labels = labelEmbedding1 ∘ raw41724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41724step2 raw41724step2Labels raw41724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw41725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41725Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41725step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41725 raw41725Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw41725 raw41725Labels = mixedMoment B raw41725step0 raw41725step0Labels := by
      have hz : ∀ j, raw41725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41725step0 = (fun i j => raw41725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41725step0 raw41725; decide +kernel
      have hl : raw41725step0Labels = raw41725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41725 raw41725Labels permutation346 hz
    mixedMoment B raw41725step0 raw41725step0Labels = mixedMoment B raw41725step1 raw41725step1Labels := by
      have ha : raw41725step1 = (fun i j => raw41725step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41725step1 raw41725step0; decide +kernel
      have hl : raw41725step1Labels = raw41725step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41725step0 raw41725step0Labels permutation65 permutation6
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw41726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41726Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41726 raw41726Labels = mixedMoment B node2283 node2283Labels := by
  calc
    mixedMoment B raw41726 raw41726Labels = mixedMoment B raw41726step0 raw41726step0Labels := by
      have hz : ∀ j, raw41726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41726step0 = (fun i j => raw41726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41726step0 raw41726; decide +kernel
      have hl : raw41726step0Labels = raw41726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41726 raw41726Labels permutation346 hz
    mixedMoment B raw41726step0 raw41726step0Labels = mixedMoment B raw41726step1 raw41726step1Labels := by
      have ha : raw41726step1 = raw41726step0 := by apply Matrix.ext; unfold raw41726step1 raw41726step0; decide +kernel
      have hl : raw41726step0Labels = labelEmbedding1 ∘ raw41726step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41726step0 raw41726step0Labels raw41726step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2283 node2283Labels := by rfl

def raw41727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41727Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41727step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41727 raw41727Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw41727 raw41727Labels = mixedMoment B raw41727step0 raw41727step0Labels := by
      have hz : ∀ j, raw41727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41727step0 = (fun i j => raw41727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41727step0 raw41727; decide +kernel
      have hl : raw41727step0Labels = raw41727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41727 raw41727Labels permutation346 hz
    mixedMoment B raw41727step0 raw41727step0Labels = mixedMoment B raw41727step1 raw41727step1Labels := by
      have ha : raw41727step1 = (fun i j => raw41727step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41727step1 raw41727step0; decide +kernel
      have hl : raw41727step1Labels = raw41727step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41727step0 raw41727step0Labels permutation65 permutation6
    _ = mixedMoment B node4886 node4886Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
