import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5120step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5120 raw5120Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw5120 raw5120Labels = mixedMoment B raw5120step0 raw5120step0Labels := by
      have hz : ∀ j, raw5120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5120step0 = (fun i j => raw5120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5120step0 raw5120; decide +kernel
      have hl : raw5120step0Labels = raw5120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5120 raw5120Labels permutation346 hz
    mixedMoment B raw5120step0 raw5120step0Labels = mixedMoment B raw5120step1 raw5120step1Labels := by
      have hz : ∀ j, raw5120step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5120step1 = (fun i j => raw5120step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5120step1 raw5120step0; decide +kernel
      have hl : raw5120step1Labels = raw5120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5120step0 raw5120step0Labels permutation56 hz
    mixedMoment B raw5120step1 raw5120step1Labels = mixedMoment B raw5120step2 raw5120step2Labels := by
      have ha : raw5120step2 = (fun i j => raw5120step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5120step2 raw5120step1; decide +kernel
      have hl : raw5120step2Labels = raw5120step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5120step1 raw5120step1Labels permutation10 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw5121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5121step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw5121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5121 raw5121Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw5121 raw5121Labels = mixedMoment B raw5121step0 raw5121step0Labels := by
      have hz : ∀ j, raw5121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5121step0 = (fun i j => raw5121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5121step0 raw5121; decide +kernel
      have hl : raw5121step0Labels = raw5121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121 raw5121Labels permutation434 hz
    mixedMoment B raw5121step0 raw5121step0Labels = mixedMoment B raw5121step1 raw5121step1Labels := by
      have hz : ∀ j, raw5121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5121step1 = (fun i j => raw5121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5121step1 raw5121step0; decide +kernel
      have hl : raw5121step1Labels = raw5121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121step0 raw5121step0Labels permutation80 hz
    mixedMoment B raw5121step1 raw5121step1Labels = mixedMoment B raw5121step2 raw5121step2Labels := by
      have hz : ∀ j, raw5121step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5121step2 = (fun i j => raw5121step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5121step2 raw5121step1; decide +kernel
      have hl : raw5121step2Labels = raw5121step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121step1 raw5121step1Labels permutation14 hz
    _ = mixedMoment B node4621 node4621Labels := by rfl

def raw5122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5122step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5122step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5122step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5122 raw5122Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5122 raw5122Labels = mixedMoment B raw5122step0 raw5122step0Labels := by
      have hz : ∀ j, raw5122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5122step0 = (fun i j => raw5122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5122step0 raw5122; decide +kernel
      have hl : raw5122step0Labels = raw5122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5122 raw5122Labels permutation434 hz
    mixedMoment B raw5122step0 raw5122step0Labels = mixedMoment B raw5122step1 raw5122step1Labels := by
      have hz : ∀ j, raw5122step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5122step1 = (fun i j => raw5122step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5122step1 raw5122step0; decide +kernel
      have hl : raw5122step1Labels = raw5122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5122step0 raw5122step0Labels permutation80 hz
    mixedMoment B raw5122step1 raw5122step1Labels = mixedMoment B raw5122step2 raw5122step2Labels := by
      have ha : raw5122step2 = (fun i j => raw5122step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5122step2 raw5122step1; decide +kernel
      have hl : raw5122step2Labels = raw5122step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5122step1 raw5122step1Labels permutation31 permutation2
    mixedMoment B raw5122step2 raw5122step2Labels = mixedMoment B raw5122step3 raw5122step3Labels := by
      have ha : raw5122step3 = -raw5122step2 := by apply Matrix.ext; change ∀ i j, raw5122step3 i j = -(raw5122step2 i j); unfold raw5122step3 raw5122step2; decide +kernel
      have hl : raw5122step3Labels = raw5122step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw5123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5123step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5123step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5123 raw5123Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5123 raw5123Labels = mixedMoment B raw5123step0 raw5123step0Labels := by
      have hz : ∀ j, raw5123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5123step0 = (fun i j => raw5123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5123step0 raw5123; decide +kernel
      have hl : raw5123step0Labels = raw5123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5123 raw5123Labels permutation434 hz
    mixedMoment B raw5123step0 raw5123step0Labels = mixedMoment B raw5123step1 raw5123step1Labels := by
      have hz : ∀ j, raw5123step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5123step1 = (fun i j => raw5123step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5123step1 raw5123step0; decide +kernel
      have hl : raw5123step1Labels = raw5123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5123step0 raw5123step0Labels permutation56 hz
    mixedMoment B raw5123step1 raw5123step1Labels = mixedMoment B raw5123step2 raw5123step2Labels := by
      have ha : raw5123step2 = (fun i j => raw5123step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5123step2 raw5123step1; decide +kernel
      have hl : raw5123step2Labels = raw5123step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5123step1 raw5123step1Labels permutation31 permutation2
    mixedMoment B raw5123step2 raw5123step2Labels = mixedMoment B raw5123step3 raw5123step3Labels := by
      have ha : raw5123step3 = -raw5123step2 := by apply Matrix.ext; change ∀ i j, raw5123step3 i j = -(raw5123step2 i j); unfold raw5123step3 raw5123step2; decide +kernel
      have hl : raw5123step3Labels = raw5123step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw5124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5124step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5124step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5124step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5124 raw5124Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5124 raw5124Labels = mixedMoment B raw5124step0 raw5124step0Labels := by
      have hz : ∀ j, raw5124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5124step0 = (fun i j => raw5124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5124step0 raw5124; decide +kernel
      have hl : raw5124step0Labels = raw5124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5124 raw5124Labels permutation346 hz
    mixedMoment B raw5124step0 raw5124step0Labels = mixedMoment B raw5124step1 raw5124step1Labels := by
      have hz : ∀ j, raw5124step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5124step1 = (fun i j => raw5124step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5124step1 raw5124step0; decide +kernel
      have hl : raw5124step1Labels = raw5124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5124step0 raw5124step0Labels permutation56 hz
    mixedMoment B raw5124step1 raw5124step1Labels = mixedMoment B raw5124step2 raw5124step2Labels := by
      have ha : raw5124step2 = (fun i j => raw5124step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5124step2 raw5124step1; decide +kernel
      have hl : raw5124step2Labels = raw5124step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5124step1 raw5124step1Labels permutation31 permutation2
    mixedMoment B raw5124step2 raw5124step2Labels = mixedMoment B raw5124step3 raw5124step3Labels := by
      have ha : raw5124step3 = -raw5124step2 := by apply Matrix.ext; change ∀ i j, raw5124step3 i j = -(raw5124step2 i j); unfold raw5124step3 raw5124step2; decide +kernel
      have hl : raw5124step3Labels = raw5124step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw5125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5125step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw5125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5125 raw5125Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw5125 raw5125Labels = mixedMoment B raw5125step0 raw5125step0Labels := by
      have hz : ∀ j, raw5125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5125step0 = (fun i j => raw5125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5125step0 raw5125; decide +kernel
      have hl : raw5125step0Labels = raw5125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125 raw5125Labels permutation434 hz
    mixedMoment B raw5125step0 raw5125step0Labels = mixedMoment B raw5125step1 raw5125step1Labels := by
      have hz : ∀ j, raw5125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5125step1 = (fun i j => raw5125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5125step1 raw5125step0; decide +kernel
      have hl : raw5125step1Labels = raw5125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125step0 raw5125step0Labels permutation80 hz
    mixedMoment B raw5125step1 raw5125step1Labels = mixedMoment B raw5125step2 raw5125step2Labels := by
      have hz : ∀ j, raw5125step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5125step2 = (fun i j => raw5125step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5125step2 raw5125step1; decide +kernel
      have hl : raw5125step2Labels = raw5125step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125step1 raw5125step1Labels permutation14 hz
    _ = mixedMoment B node5305 node5305Labels := by rfl

def raw5126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5126step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw5126step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5126step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw5126step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5126step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw5126step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5126 raw5126Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw5126 raw5126Labels = mixedMoment B raw5126step0 raw5126step0Labels := by
      have hz : ∀ j, raw5126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5126step0 = (fun i j => raw5126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5126step0 raw5126; decide +kernel
      have hl : raw5126step0Labels = raw5126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5126 raw5126Labels permutation434 hz
    mixedMoment B raw5126step0 raw5126step0Labels = mixedMoment B raw5126step1 raw5126step1Labels := by
      have hz : ∀ j, raw5126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5126step1 = (fun i j => raw5126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5126step1 raw5126step0; decide +kernel
      have hl : raw5126step1Labels = raw5126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5126step0 raw5126step0Labels permutation80 hz
    mixedMoment B raw5126step1 raw5126step1Labels = mixedMoment B raw5126step2 raw5126step2Labels := by
      have hz : ∀ j, raw5126step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5126step2 = (fun i j => raw5126step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5126step2 raw5126step1; decide +kernel
      have hl : raw5126step2Labels = raw5126step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5126step1 raw5126step1Labels permutation14 hz
    mixedMoment B raw5126step2 raw5126step2Labels = mixedMoment B raw5126step3 raw5126step3Labels := by
      have ha : raw5126step3 = (fun i j => raw5126step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5126step3 raw5126step2; decide +kernel
      have hl : raw5126step3Labels = raw5126step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5126step2 raw5126step2Labels permutation7 permutation2
    mixedMoment B raw5126step3 raw5126step3Labels = mixedMoment B raw5126step4 raw5126step4Labels := by
      have ha : raw5126step4 = -raw5126step3 := by apply Matrix.ext; change ∀ i j, raw5126step4 i j = -(raw5126step3 i j); unfold raw5126step4 raw5126step3; decide +kernel
      have hl : raw5126step4Labels = raw5126step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw5127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5127step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5127step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5127 raw5127Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw5127 raw5127Labels = mixedMoment B raw5127step0 raw5127step0Labels := by
      have hz : ∀ j, raw5127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5127step0 = (fun i j => raw5127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5127step0 raw5127; decide +kernel
      have hl : raw5127step0Labels = raw5127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5127 raw5127Labels permutation434 hz
    mixedMoment B raw5127step0 raw5127step0Labels = mixedMoment B raw5127step1 raw5127step1Labels := by
      have hz : ∀ j, raw5127step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5127step1 = (fun i j => raw5127step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5127step1 raw5127step0; decide +kernel
      have hl : raw5127step1Labels = raw5127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5127step0 raw5127step0Labels permutation80 hz
    mixedMoment B raw5127step1 raw5127step1Labels = mixedMoment B raw5127step2 raw5127step2Labels := by
      have ha : raw5127step2 = (fun i j => raw5127step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5127step2 raw5127step1; decide +kernel
      have hl : raw5127step2Labels = raw5127step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5127step1 raw5127step1Labels permutation31 permutation2
    mixedMoment B raw5127step2 raw5127step2Labels = mixedMoment B raw5127step3 raw5127step3Labels := by
      have ha : raw5127step3 = -raw5127step2 := by apply Matrix.ext; change ∀ i j, raw5127step3 i j = -(raw5127step2 i j); unfold raw5127step3 raw5127step2; decide +kernel
      have hl : raw5127step3Labels = raw5127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw5128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5128step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5128 raw5128Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw5128 raw5128Labels = mixedMoment B raw5128step0 raw5128step0Labels := by
      have hz : ∀ j, raw5128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5128step0 = (fun i j => raw5128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5128step0 raw5128; decide +kernel
      have hl : raw5128step0Labels = raw5128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5128 raw5128Labels permutation434 hz
    mixedMoment B raw5128step0 raw5128step0Labels = mixedMoment B raw5128step1 raw5128step1Labels := by
      have hz : ∀ j, raw5128step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5128step1 = (fun i j => raw5128step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5128step1 raw5128step0; decide +kernel
      have hl : raw5128step1Labels = raw5128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5128step0 raw5128step0Labels permutation56 hz
    mixedMoment B raw5128step1 raw5128step1Labels = mixedMoment B raw5128step2 raw5128step2Labels := by
      have ha : raw5128step2 = (fun i j => raw5128step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5128step2 raw5128step1; decide +kernel
      have hl : raw5128step2Labels = raw5128step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5128step1 raw5128step1Labels permutation31 permutation2
    mixedMoment B raw5128step2 raw5128step2Labels = mixedMoment B raw5128step3 raw5128step3Labels := by
      have ha : raw5128step3 = -raw5128step2 := by apply Matrix.ext; change ∀ i j, raw5128step3 i j = -(raw5128step2 i j); unfold raw5128step3 raw5128step2; decide +kernel
      have hl : raw5128step3Labels = raw5128step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw5129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5129step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5129 raw5129Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw5129 raw5129Labels = mixedMoment B raw5129step0 raw5129step0Labels := by
      have hz : ∀ j, raw5129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5129step0 = (fun i j => raw5129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5129step0 raw5129; decide +kernel
      have hl : raw5129step0Labels = raw5129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5129 raw5129Labels permutation346 hz
    mixedMoment B raw5129step0 raw5129step0Labels = mixedMoment B raw5129step1 raw5129step1Labels := by
      have hz : ∀ j, raw5129step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5129step1 = (fun i j => raw5129step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5129step1 raw5129step0; decide +kernel
      have hl : raw5129step1Labels = raw5129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5129step0 raw5129step0Labels permutation56 hz
    mixedMoment B raw5129step1 raw5129step1Labels = mixedMoment B raw5129step2 raw5129step2Labels := by
      have ha : raw5129step2 = (fun i j => raw5129step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5129step2 raw5129step1; decide +kernel
      have hl : raw5129step2Labels = raw5129step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5129step1 raw5129step1Labels permutation31 permutation2
    mixedMoment B raw5129step2 raw5129step2Labels = mixedMoment B raw5129step3 raw5129step3Labels := by
      have ha : raw5129step3 = -raw5129step2 := by apply Matrix.ext; change ∀ i j, raw5129step3 i j = -(raw5129step2 i j); unfold raw5129step3 raw5129step2; decide +kernel
      have hl : raw5129step3Labels = raw5129step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw5130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5130step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw5130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5130step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-3, 1, 2]]
def raw5130step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5130step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw5130step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5130 raw5130Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw5130 raw5130Labels = mixedMoment B raw5130step0 raw5130step0Labels := by
      have hz : ∀ j, raw5130 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5130step0 = (fun i j => raw5130 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5130step0 raw5130; decide +kernel
      have hl : raw5130step0Labels = raw5130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5130 raw5130Labels permutation434 hz
    mixedMoment B raw5130step0 raw5130step0Labels = mixedMoment B raw5130step1 raw5130step1Labels := by
      have hz : ∀ j, raw5130step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5130step1 = (fun i j => raw5130step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5130step1 raw5130step0; decide +kernel
      have hl : raw5130step1Labels = raw5130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5130step0 raw5130step0Labels permutation80 hz
    mixedMoment B raw5130step1 raw5130step1Labels = mixedMoment B raw5130step2 raw5130step2Labels := by
      have hz : ∀ j, raw5130step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5130step2 = (fun i j => raw5130step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5130step2 raw5130step1; decide +kernel
      have hl : raw5130step2Labels = raw5130step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5130step1 raw5130step1Labels permutation14 hz
    mixedMoment B raw5130step2 raw5130step2Labels = mixedMoment B raw5130step3 raw5130step3Labels := by
      have ha : raw5130step3 = (fun i j => raw5130step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5130step3 raw5130step2; decide +kernel
      have hl : raw5130step3Labels = raw5130step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5130step2 raw5130step2Labels permutation7 permutation2
    mixedMoment B raw5130step3 raw5130step3Labels = mixedMoment B raw5130step4 raw5130step4Labels := by
      have ha : raw5130step4 = -raw5130step3 := by apply Matrix.ext; change ∀ i j, raw5130step4 i j = -(raw5130step3 i j); unfold raw5130step4 raw5130step3; decide +kernel
      have hl : raw5130step4Labels = raw5130step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4505 node4505Labels := by rfl

def raw5131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5131step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5131step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5131step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5131 raw5131Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw5131 raw5131Labels = mixedMoment B raw5131step0 raw5131step0Labels := by
      have hz : ∀ j, raw5131 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5131step0 = (fun i j => raw5131 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5131step0 raw5131; decide +kernel
      have hl : raw5131step0Labels = raw5131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5131 raw5131Labels permutation434 hz
    mixedMoment B raw5131step0 raw5131step0Labels = mixedMoment B raw5131step1 raw5131step1Labels := by
      have hz : ∀ j, raw5131step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5131step1 = (fun i j => raw5131step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5131step1 raw5131step0; decide +kernel
      have hl : raw5131step1Labels = raw5131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5131step0 raw5131step0Labels permutation80 hz
    mixedMoment B raw5131step1 raw5131step1Labels = mixedMoment B raw5131step2 raw5131step2Labels := by
      have ha : raw5131step2 = (fun i j => raw5131step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5131step2 raw5131step1; decide +kernel
      have hl : raw5131step2Labels = raw5131step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5131step1 raw5131step1Labels permutation29 permutation7
    mixedMoment B raw5131step2 raw5131step2Labels = mixedMoment B raw5131step3 raw5131step3Labels := by
      have ha : raw5131step3 = raw5131step2 := by apply Matrix.ext; unfold raw5131step3 raw5131step2; decide +kernel
      have hl : raw5131step2Labels = labelEmbedding1 ∘ raw5131step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5131step2 raw5131step2Labels raw5131step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw5132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5132step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5132step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5132step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5132step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5132 raw5132Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw5132 raw5132Labels = mixedMoment B raw5132step0 raw5132step0Labels := by
      have hz : ∀ j, raw5132 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5132step0 = (fun i j => raw5132 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5132step0 raw5132; decide +kernel
      have hl : raw5132step0Labels = raw5132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5132 raw5132Labels permutation434 hz
    mixedMoment B raw5132step0 raw5132step0Labels = mixedMoment B raw5132step1 raw5132step1Labels := by
      have hz : ∀ j, raw5132step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5132step1 = (fun i j => raw5132step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5132step1 raw5132step0; decide +kernel
      have hl : raw5132step1Labels = raw5132step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5132step0 raw5132step0Labels permutation56 hz
    mixedMoment B raw5132step1 raw5132step1Labels = mixedMoment B raw5132step2 raw5132step2Labels := by
      have ha : raw5132step2 = (fun i j => raw5132step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5132step2 raw5132step1; decide +kernel
      have hl : raw5132step2Labels = raw5132step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5132step1 raw5132step1Labels permutation29 permutation7
    mixedMoment B raw5132step2 raw5132step2Labels = mixedMoment B raw5132step3 raw5132step3Labels := by
      have ha : raw5132step3 = raw5132step2 := by apply Matrix.ext; unfold raw5132step3 raw5132step2; decide +kernel
      have hl : raw5132step2Labels = labelEmbedding1 ∘ raw5132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5132step2 raw5132step2Labels raw5132step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw5133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5133step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5133step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5133step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5133step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5133 raw5133Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw5133 raw5133Labels = mixedMoment B raw5133step0 raw5133step0Labels := by
      have hz : ∀ j, raw5133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5133step0 = (fun i j => raw5133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5133step0 raw5133; decide +kernel
      have hl : raw5133step0Labels = raw5133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5133 raw5133Labels permutation346 hz
    mixedMoment B raw5133step0 raw5133step0Labels = mixedMoment B raw5133step1 raw5133step1Labels := by
      have hz : ∀ j, raw5133step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5133step1 = (fun i j => raw5133step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5133step1 raw5133step0; decide +kernel
      have hl : raw5133step1Labels = raw5133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5133step0 raw5133step0Labels permutation56 hz
    mixedMoment B raw5133step1 raw5133step1Labels = mixedMoment B raw5133step2 raw5133step2Labels := by
      have ha : raw5133step2 = (fun i j => raw5133step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5133step2 raw5133step1; decide +kernel
      have hl : raw5133step2Labels = raw5133step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5133step1 raw5133step1Labels permutation29 permutation7
    mixedMoment B raw5133step2 raw5133step2Labels = mixedMoment B raw5133step3 raw5133step3Labels := by
      have ha : raw5133step3 = raw5133step2 := by apply Matrix.ext; unfold raw5133step3 raw5133step2; decide +kernel
      have hl : raw5133step2Labels = labelEmbedding1 ∘ raw5133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5133step2 raw5133step2Labels raw5133step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw5134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5134step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5134step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5134step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]
def raw5134step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5134step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw5134step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5134step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw5134step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5134step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5134step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5134 raw5134Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5134 raw5134Labels = mixedMoment B raw5134step0 raw5134step0Labels := by
      have hz : ∀ j, raw5134 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5134step0 = (fun i j => raw5134 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5134step0 raw5134; decide +kernel
      have hl : raw5134step0Labels = raw5134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5134 raw5134Labels permutation434 hz
    mixedMoment B raw5134step0 raw5134step0Labels = mixedMoment B raw5134step1 raw5134step1Labels := by
      have hz : ∀ j, raw5134step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5134step1 = (fun i j => raw5134step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5134step1 raw5134step0; decide +kernel
      have hl : raw5134step1Labels = raw5134step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5134step0 raw5134step0Labels permutation80 hz
    mixedMoment B raw5134step1 raw5134step1Labels = mixedMoment B raw5134step2 raw5134step2Labels := by
      have hz : ∀ j, raw5134step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5134step2 = (fun i j => raw5134step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5134step2 raw5134step1; decide +kernel
      have hl : raw5134step2Labels = raw5134step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5134step1 raw5134step1Labels permutation14 hz
    mixedMoment B raw5134step2 raw5134step2Labels = mixedMoment B raw5134step3 raw5134step3Labels := by
      have hz : ∀ i, raw5134step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw5134step3 = (fun i j => raw5134step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw5134step3 raw5134step2; decide +kernel
      have hl : raw5134step3Labels = (fun j => raw5134step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5134step2 raw5134step2Labels permutation4 hz
    mixedMoment B raw5134step3 raw5134step3Labels = mixedMoment B raw5134step4 raw5134step4Labels := by
      have ha : raw5134step4 = (fun i j => raw5134step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5134step4 raw5134step3; decide +kernel
      have hl : raw5134step4Labels = raw5134step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5134step3 raw5134step3Labels permutation7 permutation0
    mixedMoment B raw5134step4 raw5134step4Labels = mixedMoment B raw5134step5 raw5134step5Labels := by
      have ha : raw5134step5 = -raw5134step4 := by apply Matrix.ext; change ∀ i j, raw5134step5 i j = -(raw5134step4 i j); unfold raw5134step5 raw5134step4; decide +kernel
      have hl : raw5134step5Labels = raw5134step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw5135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5135step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5135step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5135step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw5135step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5135step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5135step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5135step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5135step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5135 raw5135Labels = mixedMoment B node2786 node2786Labels := by
  calc
    mixedMoment B raw5135 raw5135Labels = mixedMoment B raw5135step0 raw5135step0Labels := by
      have hz : ∀ j, raw5135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5135step0 = (fun i j => raw5135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5135step0 raw5135; decide +kernel
      have hl : raw5135step0Labels = raw5135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5135 raw5135Labels permutation434 hz
    mixedMoment B raw5135step0 raw5135step0Labels = mixedMoment B raw5135step1 raw5135step1Labels := by
      have hz : ∀ j, raw5135step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5135step1 = (fun i j => raw5135step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5135step1 raw5135step0; decide +kernel
      have hl : raw5135step1Labels = raw5135step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5135step0 raw5135step0Labels permutation80 hz
    mixedMoment B raw5135step1 raw5135step1Labels = mixedMoment B raw5135step2 raw5135step2Labels := by
      have hz : ∀ j, raw5135step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5135step2 = (fun i j => raw5135step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5135step2 raw5135step1; decide +kernel
      have hl : raw5135step2Labels = raw5135step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5135step1 raw5135step1Labels permutation14 hz
    mixedMoment B raw5135step2 raw5135step2Labels = mixedMoment B raw5135step3 raw5135step3Labels := by
      have ha : raw5135step3 = (fun i j => raw5135step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5135step3 raw5135step2; decide +kernel
      have hl : raw5135step3Labels = raw5135step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5135step2 raw5135step2Labels permutation7 permutation7
    mixedMoment B raw5135step3 raw5135step3Labels = mixedMoment B raw5135step4 raw5135step4Labels := by
      have ha : raw5135step4 = raw5135step3 := by apply Matrix.ext; unfold raw5135step4 raw5135step3; decide +kernel
      have hl : raw5135step3Labels = labelEmbedding1 ∘ raw5135step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5135step3 raw5135step3Labels raw5135step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2786 node2786Labels := by rfl

def raw5136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5136step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5136step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5136step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5136step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5136step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5136step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5136 raw5136Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5136 raw5136Labels = mixedMoment B raw5136step0 raw5136step0Labels := by
      have hz : ∀ j, raw5136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5136step0 = (fun i j => raw5136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5136step0 raw5136; decide +kernel
      have hl : raw5136step0Labels = raw5136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5136 raw5136Labels permutation434 hz
    mixedMoment B raw5136step0 raw5136step0Labels = mixedMoment B raw5136step1 raw5136step1Labels := by
      have hz : ∀ j, raw5136step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5136step1 = (fun i j => raw5136step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5136step1 raw5136step0; decide +kernel
      have hl : raw5136step1Labels = raw5136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5136step0 raw5136step0Labels permutation80 hz
    mixedMoment B raw5136step1 raw5136step1Labels = mixedMoment B raw5136step2 raw5136step2Labels := by
      have ha : raw5136step2 = (fun i j => raw5136step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5136step2 raw5136step1; decide +kernel
      have hl : raw5136step2Labels = raw5136step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5136step1 raw5136step1Labels permutation29 permutation7
    mixedMoment B raw5136step2 raw5136step2Labels = mixedMoment B raw5136step3 raw5136step3Labels := by
      have ha : raw5136step3 = raw5136step2 := by apply Matrix.ext; unfold raw5136step3 raw5136step2; decide +kernel
      have hl : raw5136step2Labels = labelEmbedding1 ∘ raw5136step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5136step2 raw5136step2Labels raw5136step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw5137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5137step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5137step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5137step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5137 raw5137Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5137 raw5137Labels = mixedMoment B raw5137step0 raw5137step0Labels := by
      have hz : ∀ j, raw5137 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5137step0 = (fun i j => raw5137 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5137step0 raw5137; decide +kernel
      have hl : raw5137step0Labels = raw5137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5137 raw5137Labels permutation434 hz
    mixedMoment B raw5137step0 raw5137step0Labels = mixedMoment B raw5137step1 raw5137step1Labels := by
      have ha : raw5137step1 = (fun i j => raw5137step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5137step1 raw5137step0; decide +kernel
      have hl : raw5137step1Labels = raw5137step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5137step0 raw5137step0Labels permutation137 permutation7
    mixedMoment B raw5137step1 raw5137step1Labels = mixedMoment B raw5137step2 raw5137step2Labels := by
      have ha : raw5137step2 = raw5137step1 := by apply Matrix.ext; unfold raw5137step2 raw5137step1; decide +kernel
      have hl : raw5137step1Labels = labelEmbedding1 ∘ raw5137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5137step1 raw5137step1Labels raw5137step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw5138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5138step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5138step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5138step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5138 raw5138Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5138 raw5138Labels = mixedMoment B raw5138step0 raw5138step0Labels := by
      have hz : ∀ j, raw5138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5138step0 = (fun i j => raw5138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5138step0 raw5138; decide +kernel
      have hl : raw5138step0Labels = raw5138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5138 raw5138Labels permutation346 hz
    mixedMoment B raw5138step0 raw5138step0Labels = mixedMoment B raw5138step1 raw5138step1Labels := by
      have ha : raw5138step1 = (fun i j => raw5138step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5138step1 raw5138step0; decide +kernel
      have hl : raw5138step1Labels = raw5138step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5138step0 raw5138step0Labels permutation137 permutation7
    mixedMoment B raw5138step1 raw5138step1Labels = mixedMoment B raw5138step2 raw5138step2Labels := by
      have ha : raw5138step2 = raw5138step1 := by apply Matrix.ext; unfold raw5138step2 raw5138step1; decide +kernel
      have hl : raw5138step1Labels = labelEmbedding1 ∘ raw5138step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5138step1 raw5138step1Labels raw5138step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw5139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5139step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5139step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5139step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5139step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5139step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5139 raw5139Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw5139 raw5139Labels = mixedMoment B raw5139step0 raw5139step0Labels := by
      have hz : ∀ j, raw5139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5139step0 = (fun i j => raw5139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5139step0 raw5139; decide +kernel
      have hl : raw5139step0Labels = raw5139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5139 raw5139Labels permutation434 hz
    mixedMoment B raw5139step0 raw5139step0Labels = mixedMoment B raw5139step1 raw5139step1Labels := by
      have hz : ∀ j, raw5139step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5139step1 = (fun i j => raw5139step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5139step1 raw5139step0; decide +kernel
      have hl : raw5139step1Labels = raw5139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5139step0 raw5139step0Labels permutation80 hz
    mixedMoment B raw5139step1 raw5139step1Labels = mixedMoment B raw5139step2 raw5139step2Labels := by
      have ha : raw5139step2 = (fun i j => raw5139step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5139step2 raw5139step1; decide +kernel
      have hl : raw5139step2Labels = raw5139step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5139step1 raw5139step1Labels permutation29 permutation7
    mixedMoment B raw5139step2 raw5139step2Labels = mixedMoment B raw5139step3 raw5139step3Labels := by
      have ha : raw5139step3 = raw5139step2 := by apply Matrix.ext; unfold raw5139step3 raw5139step2; decide +kernel
      have hl : raw5139step2Labels = labelEmbedding1 ∘ raw5139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5139step2 raw5139step2Labels raw5139step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw5140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5140step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5140step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5140step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5140step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5140step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5140step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5140 raw5140Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5140 raw5140Labels = mixedMoment B raw5140step0 raw5140step0Labels := by
      have hz : ∀ j, raw5140 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5140step0 = (fun i j => raw5140 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5140step0 raw5140; decide +kernel
      have hl : raw5140step0Labels = raw5140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5140 raw5140Labels permutation434 hz
    mixedMoment B raw5140step0 raw5140step0Labels = mixedMoment B raw5140step1 raw5140step1Labels := by
      have hz : ∀ j, raw5140step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5140step1 = (fun i j => raw5140step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5140step1 raw5140step0; decide +kernel
      have hl : raw5140step1Labels = raw5140step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5140step0 raw5140step0Labels permutation80 hz
    mixedMoment B raw5140step1 raw5140step1Labels = mixedMoment B raw5140step2 raw5140step2Labels := by
      have ha : raw5140step2 = (fun i j => raw5140step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5140step2 raw5140step1; decide +kernel
      have hl : raw5140step2Labels = raw5140step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5140step1 raw5140step1Labels permutation29 permutation7
    mixedMoment B raw5140step2 raw5140step2Labels = mixedMoment B raw5140step3 raw5140step3Labels := by
      have ha : raw5140step3 = raw5140step2 := by apply Matrix.ext; unfold raw5140step3 raw5140step2; decide +kernel
      have hl : raw5140step2Labels = labelEmbedding1 ∘ raw5140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5140step2 raw5140step2Labels raw5140step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw5141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5141Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5141step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5141step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5141step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5141step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5141step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5141 raw5141Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5141 raw5141Labels = mixedMoment B raw5141step0 raw5141step0Labels := by
      have hz : ∀ j, raw5141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5141step0 = (fun i j => raw5141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5141step0 raw5141; decide +kernel
      have hl : raw5141step0Labels = raw5141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5141 raw5141Labels permutation434 hz
    mixedMoment B raw5141step0 raw5141step0Labels = mixedMoment B raw5141step1 raw5141step1Labels := by
      have hz : ∀ j, raw5141step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5141step1 = (fun i j => raw5141step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5141step1 raw5141step0; decide +kernel
      have hl : raw5141step1Labels = raw5141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5141step0 raw5141step0Labels permutation56 hz
    mixedMoment B raw5141step1 raw5141step1Labels = mixedMoment B raw5141step2 raw5141step2Labels := by
      have ha : raw5141step2 = (fun i j => raw5141step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5141step2 raw5141step1; decide +kernel
      have hl : raw5141step2Labels = raw5141step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5141step1 raw5141step1Labels permutation29 permutation7
    mixedMoment B raw5141step2 raw5141step2Labels = mixedMoment B raw5141step3 raw5141step3Labels := by
      have ha : raw5141step3 = raw5141step2 := by apply Matrix.ext; unfold raw5141step3 raw5141step2; decide +kernel
      have hl : raw5141step2Labels = labelEmbedding1 ∘ raw5141step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5141step2 raw5141step2Labels raw5141step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw5142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5142step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5142step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5142step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5142 raw5142Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5142 raw5142Labels = mixedMoment B raw5142step0 raw5142step0Labels := by
      have hz : ∀ j, raw5142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5142step0 = (fun i j => raw5142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5142step0 raw5142; decide +kernel
      have hl : raw5142step0Labels = raw5142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5142 raw5142Labels permutation434 hz
    mixedMoment B raw5142step0 raw5142step0Labels = mixedMoment B raw5142step1 raw5142step1Labels := by
      have ha : raw5142step1 = (fun i j => raw5142step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5142step1 raw5142step0; decide +kernel
      have hl : raw5142step1Labels = raw5142step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5142step0 raw5142step0Labels permutation143 permutation7
    mixedMoment B raw5142step1 raw5142step1Labels = mixedMoment B raw5142step2 raw5142step2Labels := by
      have ha : raw5142step2 = raw5142step1 := by apply Matrix.ext; unfold raw5142step2 raw5142step1; decide +kernel
      have hl : raw5142step1Labels = labelEmbedding1 ∘ raw5142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5142step1 raw5142step1Labels raw5142step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw5143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5143Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5143step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5143step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5143 raw5143Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5143 raw5143Labels = mixedMoment B raw5143step0 raw5143step0Labels := by
      have hz : ∀ j, raw5143 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5143step0 = (fun i j => raw5143 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5143step0 raw5143; decide +kernel
      have hl : raw5143step0Labels = raw5143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5143 raw5143Labels permutation265 hz
    mixedMoment B raw5143step0 raw5143step0Labels = mixedMoment B raw5143step1 raw5143step1Labels := by
      have ha : raw5143step1 = (fun i j => raw5143step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5143step1 raw5143step0; decide +kernel
      have hl : raw5143step1Labels = raw5143step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5143step0 raw5143step0Labels permutation137 permutation7
    mixedMoment B raw5143step1 raw5143step1Labels = mixedMoment B raw5143step2 raw5143step2Labels := by
      have ha : raw5143step2 = raw5143step1 := by apply Matrix.ext; unfold raw5143step2 raw5143step1; decide +kernel
      have hl : raw5143step1Labels = labelEmbedding1 ∘ raw5143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5143step1 raw5143step1Labels raw5143step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw5144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5144Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5144step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5144step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5144step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5144step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5144step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5144 raw5144Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw5144 raw5144Labels = mixedMoment B raw5144step0 raw5144step0Labels := by
      have hz : ∀ j, raw5144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5144step0 = (fun i j => raw5144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5144step0 raw5144; decide +kernel
      have hl : raw5144step0Labels = raw5144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5144 raw5144Labels permutation434 hz
    mixedMoment B raw5144step0 raw5144step0Labels = mixedMoment B raw5144step1 raw5144step1Labels := by
      have hz : ∀ j, raw5144step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5144step1 = (fun i j => raw5144step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5144step1 raw5144step0; decide +kernel
      have hl : raw5144step1Labels = raw5144step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5144step0 raw5144step0Labels permutation56 hz
    mixedMoment B raw5144step1 raw5144step1Labels = mixedMoment B raw5144step2 raw5144step2Labels := by
      have ha : raw5144step2 = (fun i j => raw5144step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5144step2 raw5144step1; decide +kernel
      have hl : raw5144step2Labels = raw5144step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5144step1 raw5144step1Labels permutation29 permutation7
    mixedMoment B raw5144step2 raw5144step2Labels = mixedMoment B raw5144step3 raw5144step3Labels := by
      have ha : raw5144step3 = raw5144step2 := by apply Matrix.ext; unfold raw5144step3 raw5144step2; decide +kernel
      have hl : raw5144step2Labels = labelEmbedding1 ∘ raw5144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5144step2 raw5144step2Labels raw5144step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw5145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5145Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5145step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5145step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5145step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5145step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5145step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5145 raw5145Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5145 raw5145Labels = mixedMoment B raw5145step0 raw5145step0Labels := by
      have hz : ∀ j, raw5145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5145step0 = (fun i j => raw5145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5145step0 raw5145; decide +kernel
      have hl : raw5145step0Labels = raw5145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5145 raw5145Labels permutation434 hz
    mixedMoment B raw5145step0 raw5145step0Labels = mixedMoment B raw5145step1 raw5145step1Labels := by
      have hz : ∀ j, raw5145step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5145step1 = (fun i j => raw5145step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5145step1 raw5145step0; decide +kernel
      have hl : raw5145step1Labels = raw5145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5145step0 raw5145step0Labels permutation56 hz
    mixedMoment B raw5145step1 raw5145step1Labels = mixedMoment B raw5145step2 raw5145step2Labels := by
      have ha : raw5145step2 = (fun i j => raw5145step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5145step2 raw5145step1; decide +kernel
      have hl : raw5145step2Labels = raw5145step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5145step1 raw5145step1Labels permutation29 permutation7
    mixedMoment B raw5145step2 raw5145step2Labels = mixedMoment B raw5145step3 raw5145step3Labels := by
      have ha : raw5145step3 = raw5145step2 := by apply Matrix.ext; unfold raw5145step3 raw5145step2; decide +kernel
      have hl : raw5145step2Labels = labelEmbedding1 ∘ raw5145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5145step2 raw5145step2Labels raw5145step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw5146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5146step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5146step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5146step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5146step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5146step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5146 raw5146Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw5146 raw5146Labels = mixedMoment B raw5146step0 raw5146step0Labels := by
      have hz : ∀ j, raw5146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5146step0 = (fun i j => raw5146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5146step0 raw5146; decide +kernel
      have hl : raw5146step0Labels = raw5146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5146 raw5146Labels permutation346 hz
    mixedMoment B raw5146step0 raw5146step0Labels = mixedMoment B raw5146step1 raw5146step1Labels := by
      have hz : ∀ j, raw5146step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5146step1 = (fun i j => raw5146step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5146step1 raw5146step0; decide +kernel
      have hl : raw5146step1Labels = raw5146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5146step0 raw5146step0Labels permutation56 hz
    mixedMoment B raw5146step1 raw5146step1Labels = mixedMoment B raw5146step2 raw5146step2Labels := by
      have ha : raw5146step2 = (fun i j => raw5146step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5146step2 raw5146step1; decide +kernel
      have hl : raw5146step2Labels = raw5146step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5146step1 raw5146step1Labels permutation29 permutation7
    mixedMoment B raw5146step2 raw5146step2Labels = mixedMoment B raw5146step3 raw5146step3Labels := by
      have ha : raw5146step3 = raw5146step2 := by apply Matrix.ext; unfold raw5146step3 raw5146step2; decide +kernel
      have hl : raw5146step2Labels = labelEmbedding1 ∘ raw5146step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5146step2 raw5146step2Labels raw5146step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw5147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5147step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5147 raw5147Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5147 raw5147Labels = mixedMoment B raw5147step0 raw5147step0Labels := by
      have hz : ∀ j, raw5147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5147step0 = (fun i j => raw5147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5147step0 raw5147; decide +kernel
      have hl : raw5147step0Labels = raw5147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5147 raw5147Labels permutation346 hz
    mixedMoment B raw5147step0 raw5147step0Labels = mixedMoment B raw5147step1 raw5147step1Labels := by
      have ha : raw5147step1 = (fun i j => raw5147step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5147step1 raw5147step0; decide +kernel
      have hl : raw5147step1Labels = raw5147step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5147step0 raw5147step0Labels permutation143 permutation7
    mixedMoment B raw5147step1 raw5147step1Labels = mixedMoment B raw5147step2 raw5147step2Labels := by
      have ha : raw5147step2 = raw5147step1 := by apply Matrix.ext; unfold raw5147step2 raw5147step1; decide +kernel
      have hl : raw5147step1Labels = labelEmbedding1 ∘ raw5147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5147step1 raw5147step1Labels raw5147step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw5148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5148Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5148step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5148step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5148 raw5148Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw5148 raw5148Labels = mixedMoment B raw5148step0 raw5148step0Labels := by
      have hz : ∀ j, raw5148 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5148step0 = (fun i j => raw5148 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5148step0 raw5148; decide +kernel
      have hl : raw5148step0Labels = raw5148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5148 raw5148Labels permutation265 hz
    mixedMoment B raw5148step0 raw5148step0Labels = mixedMoment B raw5148step1 raw5148step1Labels := by
      have ha : raw5148step1 = (fun i j => raw5148step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5148step1 raw5148step0; decide +kernel
      have hl : raw5148step1Labels = raw5148step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5148step0 raw5148step0Labels permutation143 permutation7
    mixedMoment B raw5148step1 raw5148step1Labels = mixedMoment B raw5148step2 raw5148step2Labels := by
      have ha : raw5148step2 = raw5148step1 := by apply Matrix.ext; unfold raw5148step2 raw5148step1; decide +kernel
      have hl : raw5148step1Labels = labelEmbedding1 ∘ raw5148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5148step1 raw5148step1Labels raw5148step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw5149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5149Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5149step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5149step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5149step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5149step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5149step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5149 raw5149Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw5149 raw5149Labels = mixedMoment B raw5149step0 raw5149step0Labels := by
      have hz : ∀ j, raw5149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5149step0 = (fun i j => raw5149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5149step0 raw5149; decide +kernel
      have hl : raw5149step0Labels = raw5149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5149 raw5149Labels permutation346 hz
    mixedMoment B raw5149step0 raw5149step0Labels = mixedMoment B raw5149step1 raw5149step1Labels := by
      have hz : ∀ j, raw5149step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5149step1 = (fun i j => raw5149step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5149step1 raw5149step0; decide +kernel
      have hl : raw5149step1Labels = raw5149step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5149step0 raw5149step0Labels permutation56 hz
    mixedMoment B raw5149step1 raw5149step1Labels = mixedMoment B raw5149step2 raw5149step2Labels := by
      have ha : raw5149step2 = (fun i j => raw5149step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5149step2 raw5149step1; decide +kernel
      have hl : raw5149step2Labels = raw5149step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5149step1 raw5149step1Labels permutation29 permutation7
    mixedMoment B raw5149step2 raw5149step2Labels = mixedMoment B raw5149step3 raw5149step3Labels := by
      have ha : raw5149step3 = raw5149step2 := by apply Matrix.ext; unfold raw5149step3 raw5149step2; decide +kernel
      have hl : raw5149step2Labels = labelEmbedding1 ∘ raw5149step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5149step2 raw5149step2Labels raw5149step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw5150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5150Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5150step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5150step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5150step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5150step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5150step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5150step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5150 raw5150Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5150 raw5150Labels = mixedMoment B raw5150step0 raw5150step0Labels := by
      have hz : ∀ j, raw5150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5150step0 = (fun i j => raw5150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5150step0 raw5150; decide +kernel
      have hl : raw5150step0Labels = raw5150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5150 raw5150Labels permutation346 hz
    mixedMoment B raw5150step0 raw5150step0Labels = mixedMoment B raw5150step1 raw5150step1Labels := by
      have hz : ∀ j, raw5150step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5150step1 = (fun i j => raw5150step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5150step1 raw5150step0; decide +kernel
      have hl : raw5150step1Labels = raw5150step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5150step0 raw5150step0Labels permutation56 hz
    mixedMoment B raw5150step1 raw5150step1Labels = mixedMoment B raw5150step2 raw5150step2Labels := by
      have ha : raw5150step2 = (fun i j => raw5150step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5150step2 raw5150step1; decide +kernel
      have hl : raw5150step2Labels = raw5150step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5150step1 raw5150step1Labels permutation29 permutation7
    mixedMoment B raw5150step2 raw5150step2Labels = mixedMoment B raw5150step3 raw5150step3Labels := by
      have ha : raw5150step3 = raw5150step2 := by apply Matrix.ext; unfold raw5150step3 raw5150step2; decide +kernel
      have hl : raw5150step2Labels = labelEmbedding1 ∘ raw5150step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5150step2 raw5150step2Labels raw5150step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw5151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5151Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5151step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5151step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5151step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw5151step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5151step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw5151step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5151step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw5151step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5151 raw5151Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw5151 raw5151Labels = mixedMoment B raw5151step0 raw5151step0Labels := by
      have hz : ∀ j, raw5151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5151step0 = (fun i j => raw5151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5151step0 raw5151; decide +kernel
      have hl : raw5151step0Labels = raw5151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151 raw5151Labels permutation434 hz
    mixedMoment B raw5151step0 raw5151step0Labels = mixedMoment B raw5151step1 raw5151step1Labels := by
      have hz : ∀ j, raw5151step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5151step1 = (fun i j => raw5151step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5151step1 raw5151step0; decide +kernel
      have hl : raw5151step1Labels = raw5151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151step0 raw5151step0Labels permutation80 hz
    mixedMoment B raw5151step1 raw5151step1Labels = mixedMoment B raw5151step2 raw5151step2Labels := by
      have hz : ∀ j, raw5151step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5151step2 = (fun i j => raw5151step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5151step2 raw5151step1; decide +kernel
      have hl : raw5151step2Labels = raw5151step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5151step1 raw5151step1Labels permutation14 hz
    mixedMoment B raw5151step2 raw5151step2Labels = mixedMoment B raw5151step3 raw5151step3Labels := by
      have ha : raw5151step3 = (fun i j => raw5151step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5151step3 raw5151step2; decide +kernel
      have hl : raw5151step3Labels = raw5151step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5151step2 raw5151step2Labels permutation7 permutation7
    mixedMoment B raw5151step3 raw5151step3Labels = mixedMoment B raw5151step4 raw5151step4Labels := by
      have ha : raw5151step4 = raw5151step3 := by apply Matrix.ext; unfold raw5151step4 raw5151step3; decide +kernel
      have hl : raw5151step3Labels = labelEmbedding1 ∘ raw5151step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5151step3 raw5151step3Labels raw5151step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

def raw5152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5152Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5152step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5152step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5152step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5152step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5152step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5152 raw5152Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5152 raw5152Labels = mixedMoment B raw5152step0 raw5152step0Labels := by
      have hz : ∀ j, raw5152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5152step0 = (fun i j => raw5152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5152step0 raw5152; decide +kernel
      have hl : raw5152step0Labels = raw5152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5152 raw5152Labels permutation434 hz
    mixedMoment B raw5152step0 raw5152step0Labels = mixedMoment B raw5152step1 raw5152step1Labels := by
      have hz : ∀ j, raw5152step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5152step1 = (fun i j => raw5152step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5152step1 raw5152step0; decide +kernel
      have hl : raw5152step1Labels = raw5152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5152step0 raw5152step0Labels permutation80 hz
    mixedMoment B raw5152step1 raw5152step1Labels = mixedMoment B raw5152step2 raw5152step2Labels := by
      have ha : raw5152step2 = (fun i j => raw5152step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5152step2 raw5152step1; decide +kernel
      have hl : raw5152step2Labels = raw5152step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5152step1 raw5152step1Labels permutation29 permutation7
    mixedMoment B raw5152step2 raw5152step2Labels = mixedMoment B raw5152step3 raw5152step3Labels := by
      have ha : raw5152step3 = raw5152step2 := by apply Matrix.ext; unfold raw5152step3 raw5152step2; decide +kernel
      have hl : raw5152step2Labels = labelEmbedding1 ∘ raw5152step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5152step2 raw5152step2Labels raw5152step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw5153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5153Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5153step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5153step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5153step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5153step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5153step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5153step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5153 raw5153Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5153 raw5153Labels = mixedMoment B raw5153step0 raw5153step0Labels := by
      have hz : ∀ j, raw5153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5153step0 = (fun i j => raw5153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5153step0 raw5153; decide +kernel
      have hl : raw5153step0Labels = raw5153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5153 raw5153Labels permutation434 hz
    mixedMoment B raw5153step0 raw5153step0Labels = mixedMoment B raw5153step1 raw5153step1Labels := by
      have hz : ∀ j, raw5153step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5153step1 = (fun i j => raw5153step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5153step1 raw5153step0; decide +kernel
      have hl : raw5153step1Labels = raw5153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5153step0 raw5153step0Labels permutation56 hz
    mixedMoment B raw5153step1 raw5153step1Labels = mixedMoment B raw5153step2 raw5153step2Labels := by
      have ha : raw5153step2 = (fun i j => raw5153step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5153step2 raw5153step1; decide +kernel
      have hl : raw5153step2Labels = raw5153step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5153step1 raw5153step1Labels permutation29 permutation7
    mixedMoment B raw5153step2 raw5153step2Labels = mixedMoment B raw5153step3 raw5153step3Labels := by
      have ha : raw5153step3 = raw5153step2 := by apply Matrix.ext; unfold raw5153step3 raw5153step2; decide +kernel
      have hl : raw5153step2Labels = labelEmbedding1 ∘ raw5153step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5153step2 raw5153step2Labels raw5153step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw5154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5154Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5154step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5154step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5154step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5154step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5154step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5154 raw5154Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw5154 raw5154Labels = mixedMoment B raw5154step0 raw5154step0Labels := by
      have hz : ∀ j, raw5154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5154step0 = (fun i j => raw5154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5154step0 raw5154; decide +kernel
      have hl : raw5154step0Labels = raw5154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5154 raw5154Labels permutation346 hz
    mixedMoment B raw5154step0 raw5154step0Labels = mixedMoment B raw5154step1 raw5154step1Labels := by
      have hz : ∀ j, raw5154step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5154step1 = (fun i j => raw5154step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5154step1 raw5154step0; decide +kernel
      have hl : raw5154step1Labels = raw5154step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5154step0 raw5154step0Labels permutation56 hz
    mixedMoment B raw5154step1 raw5154step1Labels = mixedMoment B raw5154step2 raw5154step2Labels := by
      have ha : raw5154step2 = (fun i j => raw5154step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5154step2 raw5154step1; decide +kernel
      have hl : raw5154step2Labels = raw5154step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5154step1 raw5154step1Labels permutation29 permutation7
    mixedMoment B raw5154step2 raw5154step2Labels = mixedMoment B raw5154step3 raw5154step3Labels := by
      have ha : raw5154step3 = raw5154step2 := by apply Matrix.ext; unfold raw5154step3 raw5154step2; decide +kernel
      have hl : raw5154step2Labels = labelEmbedding1 ∘ raw5154step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5154step2 raw5154step2Labels raw5154step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw5155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5155Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5155step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5155step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5155step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw5155step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5155step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw5155step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5155step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw5155step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5155 raw5155Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw5155 raw5155Labels = mixedMoment B raw5155step0 raw5155step0Labels := by
      have hz : ∀ j, raw5155 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5155step0 = (fun i j => raw5155 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5155step0 raw5155; decide +kernel
      have hl : raw5155step0Labels = raw5155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5155 raw5155Labels permutation434 hz
    mixedMoment B raw5155step0 raw5155step0Labels = mixedMoment B raw5155step1 raw5155step1Labels := by
      have hz : ∀ j, raw5155step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5155step1 = (fun i j => raw5155step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5155step1 raw5155step0; decide +kernel
      have hl : raw5155step1Labels = raw5155step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5155step0 raw5155step0Labels permutation80 hz
    mixedMoment B raw5155step1 raw5155step1Labels = mixedMoment B raw5155step2 raw5155step2Labels := by
      have hz : ∀ j, raw5155step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5155step2 = (fun i j => raw5155step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5155step2 raw5155step1; decide +kernel
      have hl : raw5155step2Labels = raw5155step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5155step1 raw5155step1Labels permutation14 hz
    mixedMoment B raw5155step2 raw5155step2Labels = mixedMoment B raw5155step3 raw5155step3Labels := by
      have ha : raw5155step3 = (fun i j => raw5155step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5155step3 raw5155step2; decide +kernel
      have hl : raw5155step3Labels = raw5155step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5155step2 raw5155step2Labels permutation7 permutation7
    mixedMoment B raw5155step3 raw5155step3Labels = mixedMoment B raw5155step4 raw5155step4Labels := by
      have ha : raw5155step4 = raw5155step3 := by apply Matrix.ext; unfold raw5155step4 raw5155step3; decide +kernel
      have hl : raw5155step3Labels = labelEmbedding1 ∘ raw5155step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5155step3 raw5155step3Labels raw5155step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw5156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5156step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5156step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5156step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw5156step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5156step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw5156step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5156step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw5156step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5156 raw5156Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw5156 raw5156Labels = mixedMoment B raw5156step0 raw5156step0Labels := by
      have hz : ∀ j, raw5156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5156step0 = (fun i j => raw5156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5156step0 raw5156; decide +kernel
      have hl : raw5156step0Labels = raw5156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5156 raw5156Labels permutation434 hz
    mixedMoment B raw5156step0 raw5156step0Labels = mixedMoment B raw5156step1 raw5156step1Labels := by
      have hz : ∀ j, raw5156step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5156step1 = (fun i j => raw5156step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5156step1 raw5156step0; decide +kernel
      have hl : raw5156step1Labels = raw5156step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5156step0 raw5156step0Labels permutation80 hz
    mixedMoment B raw5156step1 raw5156step1Labels = mixedMoment B raw5156step2 raw5156step2Labels := by
      have hz : ∀ j, raw5156step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5156step2 = (fun i j => raw5156step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5156step2 raw5156step1; decide +kernel
      have hl : raw5156step2Labels = raw5156step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5156step1 raw5156step1Labels permutation14 hz
    mixedMoment B raw5156step2 raw5156step2Labels = mixedMoment B raw5156step3 raw5156step3Labels := by
      have ha : raw5156step3 = (fun i j => raw5156step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5156step3 raw5156step2; decide +kernel
      have hl : raw5156step3Labels = raw5156step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5156step2 raw5156step2Labels permutation7 permutation7
    mixedMoment B raw5156step3 raw5156step3Labels = mixedMoment B raw5156step4 raw5156step4Labels := by
      have ha : raw5156step4 = raw5156step3 := by apply Matrix.ext; unfold raw5156step4 raw5156step3; decide +kernel
      have hl : raw5156step3Labels = labelEmbedding1 ∘ raw5156step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5156step3 raw5156step3Labels raw5156step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw5157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5157Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5157step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5157step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5157step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5157step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5157step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5157 raw5157Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw5157 raw5157Labels = mixedMoment B raw5157step0 raw5157step0Labels := by
      have hz : ∀ j, raw5157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5157step0 = (fun i j => raw5157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5157step0 raw5157; decide +kernel
      have hl : raw5157step0Labels = raw5157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5157 raw5157Labels permutation434 hz
    mixedMoment B raw5157step0 raw5157step0Labels = mixedMoment B raw5157step1 raw5157step1Labels := by
      have hz : ∀ j, raw5157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5157step1 = (fun i j => raw5157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5157step1 raw5157step0; decide +kernel
      have hl : raw5157step1Labels = raw5157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5157step0 raw5157step0Labels permutation80 hz
    mixedMoment B raw5157step1 raw5157step1Labels = mixedMoment B raw5157step2 raw5157step2Labels := by
      have ha : raw5157step2 = (fun i j => raw5157step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5157step2 raw5157step1; decide +kernel
      have hl : raw5157step2Labels = raw5157step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5157step1 raw5157step1Labels permutation29 permutation7
    mixedMoment B raw5157step2 raw5157step2Labels = mixedMoment B raw5157step3 raw5157step3Labels := by
      have ha : raw5157step3 = raw5157step2 := by apply Matrix.ext; unfold raw5157step3 raw5157step2; decide +kernel
      have hl : raw5157step2Labels = labelEmbedding1 ∘ raw5157step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5157step2 raw5157step2Labels raw5157step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw5158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5158step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5158step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5158step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5158step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5158step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5158step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5158 raw5158Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw5158 raw5158Labels = mixedMoment B raw5158step0 raw5158step0Labels := by
      have hz : ∀ j, raw5158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5158step0 = (fun i j => raw5158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5158step0 raw5158; decide +kernel
      have hl : raw5158step0Labels = raw5158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5158 raw5158Labels permutation434 hz
    mixedMoment B raw5158step0 raw5158step0Labels = mixedMoment B raw5158step1 raw5158step1Labels := by
      have hz : ∀ j, raw5158step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5158step1 = (fun i j => raw5158step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5158step1 raw5158step0; decide +kernel
      have hl : raw5158step1Labels = raw5158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5158step0 raw5158step0Labels permutation56 hz
    mixedMoment B raw5158step1 raw5158step1Labels = mixedMoment B raw5158step2 raw5158step2Labels := by
      have ha : raw5158step2 = (fun i j => raw5158step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5158step2 raw5158step1; decide +kernel
      have hl : raw5158step2Labels = raw5158step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5158step1 raw5158step1Labels permutation29 permutation7
    mixedMoment B raw5158step2 raw5158step2Labels = mixedMoment B raw5158step3 raw5158step3Labels := by
      have ha : raw5158step3 = raw5158step2 := by apply Matrix.ext; unfold raw5158step3 raw5158step2; decide +kernel
      have hl : raw5158step2Labels = labelEmbedding1 ∘ raw5158step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5158step2 raw5158step2Labels raw5158step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw5159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5159step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5159step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5159step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5159step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5159 raw5159Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw5159 raw5159Labels = mixedMoment B raw5159step0 raw5159step0Labels := by
      have hz : ∀ j, raw5159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5159step0 = (fun i j => raw5159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5159step0 raw5159; decide +kernel
      have hl : raw5159step0Labels = raw5159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5159 raw5159Labels permutation346 hz
    mixedMoment B raw5159step0 raw5159step0Labels = mixedMoment B raw5159step1 raw5159step1Labels := by
      have hz : ∀ j, raw5159step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5159step1 = (fun i j => raw5159step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5159step1 raw5159step0; decide +kernel
      have hl : raw5159step1Labels = raw5159step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5159step0 raw5159step0Labels permutation56 hz
    mixedMoment B raw5159step1 raw5159step1Labels = mixedMoment B raw5159step2 raw5159step2Labels := by
      have ha : raw5159step2 = (fun i j => raw5159step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5159step2 raw5159step1; decide +kernel
      have hl : raw5159step2Labels = raw5159step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5159step1 raw5159step1Labels permutation29 permutation7
    mixedMoment B raw5159step2 raw5159step2Labels = mixedMoment B raw5159step3 raw5159step3Labels := by
      have ha : raw5159step3 = raw5159step2 := by apply Matrix.ext; unfold raw5159step3 raw5159step2; decide +kernel
      have hl : raw5159step2Labels = labelEmbedding1 ∘ raw5159step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5159step2 raw5159step2Labels raw5159step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw5160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5160step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5160step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5160step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw5160step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5160step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw5160step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5160step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw5160step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5160 raw5160Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw5160 raw5160Labels = mixedMoment B raw5160step0 raw5160step0Labels := by
      have hz : ∀ j, raw5160 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5160step0 = (fun i j => raw5160 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5160step0 raw5160; decide +kernel
      have hl : raw5160step0Labels = raw5160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5160 raw5160Labels permutation434 hz
    mixedMoment B raw5160step0 raw5160step0Labels = mixedMoment B raw5160step1 raw5160step1Labels := by
      have hz : ∀ j, raw5160step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5160step1 = (fun i j => raw5160step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5160step1 raw5160step0; decide +kernel
      have hl : raw5160step1Labels = raw5160step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5160step0 raw5160step0Labels permutation80 hz
    mixedMoment B raw5160step1 raw5160step1Labels = mixedMoment B raw5160step2 raw5160step2Labels := by
      have hz : ∀ j, raw5160step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5160step2 = (fun i j => raw5160step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5160step2 raw5160step1; decide +kernel
      have hl : raw5160step2Labels = raw5160step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5160step1 raw5160step1Labels permutation14 hz
    mixedMoment B raw5160step2 raw5160step2Labels = mixedMoment B raw5160step3 raw5160step3Labels := by
      have ha : raw5160step3 = (fun i j => raw5160step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5160step3 raw5160step2; decide +kernel
      have hl : raw5160step3Labels = raw5160step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5160step2 raw5160step2Labels permutation7 permutation7
    mixedMoment B raw5160step3 raw5160step3Labels = mixedMoment B raw5160step4 raw5160step4Labels := by
      have ha : raw5160step4 = raw5160step3 := by apply Matrix.ext; unfold raw5160step4 raw5160step3; decide +kernel
      have hl : raw5160step3Labels = labelEmbedding1 ∘ raw5160step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5160step3 raw5160step3Labels raw5160step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1754 node1754Labels := by rfl

def raw5161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5161step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw5161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5161step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw5161step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5161step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5161step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5161 raw5161Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw5161 raw5161Labels = mixedMoment B raw5161step0 raw5161step0Labels := by
      have hz : ∀ j, raw5161 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5161step0 = (fun i j => raw5161 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5161step0 raw5161; decide +kernel
      have hl : raw5161step0Labels = raw5161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5161 raw5161Labels permutation434 hz
    mixedMoment B raw5161step0 raw5161step0Labels = mixedMoment B raw5161step1 raw5161step1Labels := by
      have hz : ∀ j, raw5161step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5161step1 = (fun i j => raw5161step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5161step1 raw5161step0; decide +kernel
      have hl : raw5161step1Labels = raw5161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5161step0 raw5161step0Labels permutation80 hz
    mixedMoment B raw5161step1 raw5161step1Labels = mixedMoment B raw5161step2 raw5161step2Labels := by
      have hz : ∀ j, raw5161step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5161step2 = (fun i j => raw5161step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5161step2 raw5161step1; decide +kernel
      have hl : raw5161step2Labels = raw5161step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5161step1 raw5161step1Labels permutation14 hz
    mixedMoment B raw5161step2 raw5161step2Labels = mixedMoment B raw5161step3 raw5161step3Labels := by
      have ha : raw5161step3 = (fun i j => raw5161step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5161step3 raw5161step2; decide +kernel
      have hl : raw5161step3Labels = raw5161step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5161step2 raw5161step2Labels permutation7 permutation2
    mixedMoment B raw5161step3 raw5161step3Labels = mixedMoment B raw5161step4 raw5161step4Labels := by
      have ha : raw5161step4 = -raw5161step3 := by apply Matrix.ext; change ∀ i j, raw5161step4 i j = -(raw5161step3 i j); unfold raw5161step4 raw5161step3; decide +kernel
      have hl : raw5161step4Labels = raw5161step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw5162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5162step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5162 raw5162Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw5162 raw5162Labels = mixedMoment B raw5162step0 raw5162step0Labels := by
      have hz : ∀ j, raw5162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5162step0 = (fun i j => raw5162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5162step0 raw5162; decide +kernel
      have hl : raw5162step0Labels = raw5162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5162 raw5162Labels permutation434 hz
    mixedMoment B raw5162step0 raw5162step0Labels = mixedMoment B raw5162step1 raw5162step1Labels := by
      have hz : ∀ j, raw5162step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5162step1 = (fun i j => raw5162step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5162step1 raw5162step0; decide +kernel
      have hl : raw5162step1Labels = raw5162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5162step0 raw5162step0Labels permutation80 hz
    mixedMoment B raw5162step1 raw5162step1Labels = mixedMoment B raw5162step2 raw5162step2Labels := by
      have ha : raw5162step2 = (fun i j => raw5162step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5162step2 raw5162step1; decide +kernel
      have hl : raw5162step2Labels = raw5162step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5162step1 raw5162step1Labels permutation10 permutation2
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw5163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5163Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5163 raw5163Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw5163 raw5163Labels = mixedMoment B raw5163step0 raw5163step0Labels := by
      have hz : ∀ j, raw5163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5163step0 = (fun i j => raw5163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5163step0 raw5163; decide +kernel
      have hl : raw5163step0Labels = raw5163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5163 raw5163Labels permutation434 hz
    mixedMoment B raw5163step0 raw5163step0Labels = mixedMoment B raw5163step1 raw5163step1Labels := by
      have hz : ∀ j, raw5163step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5163step1 = (fun i j => raw5163step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5163step1 raw5163step0; decide +kernel
      have hl : raw5163step1Labels = raw5163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5163step0 raw5163step0Labels permutation56 hz
    mixedMoment B raw5163step1 raw5163step1Labels = mixedMoment B raw5163step2 raw5163step2Labels := by
      have ha : raw5163step2 = (fun i j => raw5163step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5163step2 raw5163step1; decide +kernel
      have hl : raw5163step2Labels = raw5163step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5163step1 raw5163step1Labels permutation10 permutation2
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw5164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5164step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5164 raw5164Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw5164 raw5164Labels = mixedMoment B raw5164step0 raw5164step0Labels := by
      have hz : ∀ j, raw5164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5164step0 = (fun i j => raw5164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5164step0 raw5164; decide +kernel
      have hl : raw5164step0Labels = raw5164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5164 raw5164Labels permutation346 hz
    mixedMoment B raw5164step0 raw5164step0Labels = mixedMoment B raw5164step1 raw5164step1Labels := by
      have hz : ∀ j, raw5164step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5164step1 = (fun i j => raw5164step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5164step1 raw5164step0; decide +kernel
      have hl : raw5164step1Labels = raw5164step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5164step0 raw5164step0Labels permutation56 hz
    mixedMoment B raw5164step1 raw5164step1Labels = mixedMoment B raw5164step2 raw5164step2Labels := by
      have ha : raw5164step2 = (fun i j => raw5164step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5164step2 raw5164step1; decide +kernel
      have hl : raw5164step2Labels = raw5164step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5164step1 raw5164step1Labels permutation10 permutation2
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw5165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5165step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw5165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5165 raw5165Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw5165 raw5165Labels = mixedMoment B raw5165step0 raw5165step0Labels := by
      have hz : ∀ j, raw5165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5165step0 = (fun i j => raw5165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5165step0 raw5165; decide +kernel
      have hl : raw5165step0Labels = raw5165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165 raw5165Labels permutation434 hz
    mixedMoment B raw5165step0 raw5165step0Labels = mixedMoment B raw5165step1 raw5165step1Labels := by
      have hz : ∀ j, raw5165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5165step1 = (fun i j => raw5165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5165step1 raw5165step0; decide +kernel
      have hl : raw5165step1Labels = raw5165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165step0 raw5165step0Labels permutation80 hz
    mixedMoment B raw5165step1 raw5165step1Labels = mixedMoment B raw5165step2 raw5165step2Labels := by
      have hz : ∀ j, raw5165step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5165step2 = (fun i j => raw5165step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5165step2 raw5165step1; decide +kernel
      have hl : raw5165step2Labels = raw5165step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5165step1 raw5165step1Labels permutation14 hz
    _ = mixedMoment B node1297 node1297Labels := by rfl

def raw5166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5166Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5166step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw5166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5166step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw5166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5166step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw5166step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5166 raw5166Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw5166 raw5166Labels = mixedMoment B raw5166step0 raw5166step0Labels := by
      have hz : ∀ j, raw5166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5166step0 = (fun i j => raw5166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5166step0 raw5166; decide +kernel
      have hl : raw5166step0Labels = raw5166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5166 raw5166Labels permutation434 hz
    mixedMoment B raw5166step0 raw5166step0Labels = mixedMoment B raw5166step1 raw5166step1Labels := by
      have hz : ∀ j, raw5166step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5166step1 = (fun i j => raw5166step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5166step1 raw5166step0; decide +kernel
      have hl : raw5166step1Labels = raw5166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5166step0 raw5166step0Labels permutation80 hz
    mixedMoment B raw5166step1 raw5166step1Labels = mixedMoment B raw5166step2 raw5166step2Labels := by
      have hz : ∀ j, raw5166step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5166step2 = (fun i j => raw5166step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5166step2 raw5166step1; decide +kernel
      have hl : raw5166step2Labels = raw5166step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5166step1 raw5166step1Labels permutation14 hz
    mixedMoment B raw5166step2 raw5166step2Labels = mixedMoment B raw5166step3 raw5166step3Labels := by
      have ha : raw5166step3 = (fun i j => raw5166step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5166step3 raw5166step2; decide +kernel
      have hl : raw5166step3Labels = raw5166step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5166step2 raw5166step2Labels permutation7 permutation2
    mixedMoment B raw5166step3 raw5166step3Labels = mixedMoment B raw5166step4 raw5166step4Labels := by
      have ha : raw5166step4 = -raw5166step3 := by apply Matrix.ext; change ∀ i j, raw5166step4 i j = -(raw5166step3 i j); unfold raw5166step4 raw5166step3; decide +kernel
      have hl : raw5166step4Labels = raw5166step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw5167 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![3, -3]]
def raw5167Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5167step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![3, -3]]
def raw5167step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5167step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]
def raw5167step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5167step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw5167step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5167step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw5167step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5167step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5167step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5167 raw5167Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5167 raw5167Labels = mixedMoment B raw5167step0 raw5167step0Labels := by
      have hz : ∀ j, raw5167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5167step0 = (fun i j => raw5167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5167step0 raw5167; decide +kernel
      have hl : raw5167step0Labels = raw5167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167 raw5167Labels permutation434 hz
    mixedMoment B raw5167step0 raw5167step0Labels = mixedMoment B raw5167step1 raw5167step1Labels := by
      have hz : ∀ j, raw5167step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5167step1 = (fun i j => raw5167step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5167step1 raw5167step0; decide +kernel
      have hl : raw5167step1Labels = raw5167step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167step0 raw5167step0Labels permutation80 hz
    mixedMoment B raw5167step1 raw5167step1Labels = mixedMoment B raw5167step2 raw5167step2Labels := by
      have hz : ∀ j, raw5167step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5167step2 = (fun i j => raw5167step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5167step2 raw5167step1; decide +kernel
      have hl : raw5167step2Labels = raw5167step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5167step1 raw5167step1Labels permutation14 hz
    mixedMoment B raw5167step2 raw5167step2Labels = mixedMoment B raw5167step3 raw5167step3Labels := by
      have ha : raw5167step3 = (fun i j => raw5167step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5167step3 raw5167step2; decide +kernel
      have hl : raw5167step3Labels = raw5167step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5167step2 raw5167step2Labels permutation7 permutation0
    mixedMoment B raw5167step3 raw5167step3Labels = mixedMoment B raw5167step4 raw5167step4Labels := by
      have ha : raw5167step4 = -raw5167step3 := by apply Matrix.ext; change ∀ i j, raw5167step4 i j = -(raw5167step3 i j); unfold raw5167step4 raw5167step3; decide +kernel
      have hl : raw5167step4Labels = raw5167step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw5168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5168 raw5168Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw5168 raw5168Labels = mixedMoment B raw5168step0 raw5168step0Labels := by
      have hz : ∀ j, raw5168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5168step0 = (fun i j => raw5168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5168step0 raw5168; decide +kernel
      have hl : raw5168step0Labels = raw5168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5168 raw5168Labels permutation434 hz
    mixedMoment B raw5168step0 raw5168step0Labels = mixedMoment B raw5168step1 raw5168step1Labels := by
      have ha : raw5168step1 = (fun i j => raw5168step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5168step1 raw5168step0; decide +kernel
      have hl : raw5168step1Labels = raw5168step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5168step0 raw5168step0Labels permutation139 permutation2
    mixedMoment B raw5168step1 raw5168step1Labels = mixedMoment B raw5168step2 raw5168step2Labels := by
      have ha : raw5168step2 = -raw5168step1 := by apply Matrix.ext; change ∀ i j, raw5168step2 i j = -(raw5168step1 i j); unfold raw5168step2 raw5168step1; decide +kernel
      have hl : raw5168step2Labels = raw5168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw5169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5169 raw5169Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw5169 raw5169Labels = mixedMoment B raw5169step0 raw5169step0Labels := by
      have hz : ∀ j, raw5169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5169step0 = (fun i j => raw5169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5169step0 raw5169; decide +kernel
      have hl : raw5169step0Labels = raw5169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5169 raw5169Labels permutation346 hz
    mixedMoment B raw5169step0 raw5169step0Labels = mixedMoment B raw5169step1 raw5169step1Labels := by
      have ha : raw5169step1 = (fun i j => raw5169step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5169step1 raw5169step0; decide +kernel
      have hl : raw5169step1Labels = raw5169step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5169step0 raw5169step0Labels permutation139 permutation2
    mixedMoment B raw5169step1 raw5169step1Labels = mixedMoment B raw5169step2 raw5169step2Labels := by
      have ha : raw5169step2 = -raw5169step1 := by apply Matrix.ext; change ∀ i j, raw5169step2 i j = -(raw5169step1 i j); unfold raw5169step2 raw5169step1; decide +kernel
      have hl : raw5169step2Labels = raw5169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw5170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5170step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw5170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5170 raw5170Labels = mixedMoment B node2060 node2060Labels := by
  calc
    mixedMoment B raw5170 raw5170Labels = mixedMoment B raw5170step0 raw5170step0Labels := by
      have hz : ∀ j, raw5170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5170step0 = (fun i j => raw5170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5170step0 raw5170; decide +kernel
      have hl : raw5170step0Labels = raw5170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5170 raw5170Labels permutation434 hz
    mixedMoment B raw5170step0 raw5170step0Labels = mixedMoment B raw5170step1 raw5170step1Labels := by
      have hz : ∀ j, raw5170step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5170step1 = (fun i j => raw5170step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5170step1 raw5170step0; decide +kernel
      have hl : raw5170step1Labels = raw5170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5170step0 raw5170step0Labels permutation80 hz
    mixedMoment B raw5170step1 raw5170step1Labels = mixedMoment B raw5170step2 raw5170step2Labels := by
      have ha : raw5170step2 = (fun i j => raw5170step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5170step2 raw5170step1; decide +kernel
      have hl : raw5170step2Labels = raw5170step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5170step1 raw5170step1Labels permutation29 permutation2
    mixedMoment B raw5170step2 raw5170step2Labels = mixedMoment B raw5170step3 raw5170step3Labels := by
      have ha : raw5170step3 = -raw5170step2 := by apply Matrix.ext; change ∀ i j, raw5170step3 i j = -(raw5170step2 i j); unfold raw5170step3 raw5170step2; decide +kernel
      have hl : raw5170step3Labels = raw5170step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2060 node2060Labels := by rfl

def raw5171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5171 raw5171Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5171 raw5171Labels = mixedMoment B raw5171step0 raw5171step0Labels := by
      have hz : ∀ j, raw5171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5171step0 = (fun i j => raw5171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5171step0 raw5171; decide +kernel
      have hl : raw5171step0Labels = raw5171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5171 raw5171Labels permutation434 hz
    mixedMoment B raw5171step0 raw5171step0Labels = mixedMoment B raw5171step1 raw5171step1Labels := by
      have hz : ∀ j, raw5171step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5171step1 = (fun i j => raw5171step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5171step1 raw5171step0; decide +kernel
      have hl : raw5171step1Labels = raw5171step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5171step0 raw5171step0Labels permutation80 hz
    mixedMoment B raw5171step1 raw5171step1Labels = mixedMoment B raw5171step2 raw5171step2Labels := by
      have ha : raw5171step2 = (fun i j => raw5171step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5171step2 raw5171step1; decide +kernel
      have hl : raw5171step2Labels = raw5171step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5171step1 raw5171step1Labels permutation10 permutation2
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw5172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw5172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5172step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5172 raw5172Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw5172 raw5172Labels = mixedMoment B raw5172step0 raw5172step0Labels := by
      have hz : ∀ j, raw5172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5172step0 = (fun i j => raw5172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5172step0 raw5172; decide +kernel
      have hl : raw5172step0Labels = raw5172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5172 raw5172Labels permutation434 hz
    mixedMoment B raw5172step0 raw5172step0Labels = mixedMoment B raw5172step1 raw5172step1Labels := by
      have hz : ∀ j, raw5172step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5172step1 = (fun i j => raw5172step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5172step1 raw5172step0; decide +kernel
      have hl : raw5172step1Labels = raw5172step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5172step0 raw5172step0Labels permutation80 hz
    mixedMoment B raw5172step1 raw5172step1Labels = mixedMoment B raw5172step2 raw5172step2Labels := by
      have ha : raw5172step2 = (fun i j => raw5172step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5172step2 raw5172step1; decide +kernel
      have hl : raw5172step2Labels = raw5172step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5172step1 raw5172step1Labels permutation31 permutation2
    mixedMoment B raw5172step2 raw5172step2Labels = mixedMoment B raw5172step3 raw5172step3Labels := by
      have ha : raw5172step3 = -raw5172step2 := by apply Matrix.ext; change ∀ i j, raw5172step3 i j = -(raw5172step2 i j); unfold raw5172step3 raw5172step2; decide +kernel
      have hl : raw5172step3Labels = raw5172step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw5173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5173 raw5173Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw5173 raw5173Labels = mixedMoment B raw5173step0 raw5173step0Labels := by
      have hz : ∀ j, raw5173 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5173step0 = (fun i j => raw5173 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5173step0 raw5173; decide +kernel
      have hl : raw5173step0Labels = raw5173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5173 raw5173Labels permutation434 hz
    mixedMoment B raw5173step0 raw5173step0Labels = mixedMoment B raw5173step1 raw5173step1Labels := by
      have ha : raw5173step1 = (fun i j => raw5173step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5173step1 raw5173step0; decide +kernel
      have hl : raw5173step1Labels = raw5173step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5173step0 raw5173step0Labels permutation145 permutation2
    mixedMoment B raw5173step1 raw5173step1Labels = mixedMoment B raw5173step2 raw5173step2Labels := by
      have ha : raw5173step2 = -raw5173step1 := by apply Matrix.ext; change ∀ i j, raw5173step2 i j = -(raw5173step1 i j); unfold raw5173step2 raw5173step1; decide +kernel
      have hl : raw5173step2Labels = raw5173step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw5174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5174 raw5174Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw5174 raw5174Labels = mixedMoment B raw5174step0 raw5174step0Labels := by
      have hz : ∀ j, raw5174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5174step0 = (fun i j => raw5174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5174step0 raw5174; decide +kernel
      have hl : raw5174step0Labels = raw5174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5174 raw5174Labels permutation346 hz
    mixedMoment B raw5174step0 raw5174step0Labels = mixedMoment B raw5174step1 raw5174step1Labels := by
      have ha : raw5174step1 = (fun i j => raw5174step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5174step1 raw5174step0; decide +kernel
      have hl : raw5174step1Labels = raw5174step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5174step0 raw5174step0Labels permutation145 permutation2
    mixedMoment B raw5174step1 raw5174step1Labels = mixedMoment B raw5174step2 raw5174step2Labels := by
      have ha : raw5174step2 = -raw5174step1 := by apply Matrix.ext; change ∀ i j, raw5174step2 i j = -(raw5174step1 i j); unfold raw5174step2 raw5174step1; decide +kernel
      have hl : raw5174step2Labels = raw5174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw5175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5175step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5175 raw5175Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw5175 raw5175Labels = mixedMoment B raw5175step0 raw5175step0Labels := by
      have hz : ∀ j, raw5175 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5175step0 = (fun i j => raw5175 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5175step0 raw5175; decide +kernel
      have hl : raw5175step0Labels = raw5175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5175 raw5175Labels permutation434 hz
    mixedMoment B raw5175step0 raw5175step0Labels = mixedMoment B raw5175step1 raw5175step1Labels := by
      have hz : ∀ j, raw5175step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5175step1 = (fun i j => raw5175step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5175step1 raw5175step0; decide +kernel
      have hl : raw5175step1Labels = raw5175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5175step0 raw5175step0Labels permutation80 hz
    mixedMoment B raw5175step1 raw5175step1Labels = mixedMoment B raw5175step2 raw5175step2Labels := by
      have ha : raw5175step2 = (fun i j => raw5175step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5175step2 raw5175step1; decide +kernel
      have hl : raw5175step2Labels = raw5175step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5175step1 raw5175step1Labels permutation31 permutation2
    mixedMoment B raw5175step2 raw5175step2Labels = mixedMoment B raw5175step3 raw5175step3Labels := by
      have ha : raw5175step3 = -raw5175step2 := by apply Matrix.ext; change ∀ i j, raw5175step3 i j = -(raw5175step2 i j); unfold raw5175step3 raw5175step2; decide +kernel
      have hl : raw5175step3Labels = raw5175step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw5176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5176 raw5176Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw5176 raw5176Labels = mixedMoment B raw5176step0 raw5176step0Labels := by
      have hz : ∀ j, raw5176 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5176step0 = (fun i j => raw5176 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5176step0 raw5176; decide +kernel
      have hl : raw5176step0Labels = raw5176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5176 raw5176Labels permutation434 hz
    mixedMoment B raw5176step0 raw5176step0Labels = mixedMoment B raw5176step1 raw5176step1Labels := by
      have hz : ∀ j, raw5176step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5176step1 = (fun i j => raw5176step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5176step1 raw5176step0; decide +kernel
      have hl : raw5176step1Labels = raw5176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5176step0 raw5176step0Labels permutation80 hz
    mixedMoment B raw5176step1 raw5176step1Labels = mixedMoment B raw5176step2 raw5176step2Labels := by
      have ha : raw5176step2 = (fun i j => raw5176step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5176step2 raw5176step1; decide +kernel
      have hl : raw5176step2Labels = raw5176step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5176step1 raw5176step1Labels permutation31 permutation2
    mixedMoment B raw5176step2 raw5176step2Labels = mixedMoment B raw5176step3 raw5176step3Labels := by
      have ha : raw5176step3 = -raw5176step2 := by apply Matrix.ext; change ∀ i j, raw5176step3 i j = -(raw5176step2 i j); unfold raw5176step3 raw5176step2; decide +kernel
      have hl : raw5176step3Labels = raw5176step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw5177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5177step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5177step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5177step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5177 raw5177Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw5177 raw5177Labels = mixedMoment B raw5177step0 raw5177step0Labels := by
      have hz : ∀ j, raw5177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5177step0 = (fun i j => raw5177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5177step0 raw5177; decide +kernel
      have hl : raw5177step0Labels = raw5177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5177 raw5177Labels permutation434 hz
    mixedMoment B raw5177step0 raw5177step0Labels = mixedMoment B raw5177step1 raw5177step1Labels := by
      have hz : ∀ j, raw5177step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5177step1 = (fun i j => raw5177step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5177step1 raw5177step0; decide +kernel
      have hl : raw5177step1Labels = raw5177step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5177step0 raw5177step0Labels permutation56 hz
    mixedMoment B raw5177step1 raw5177step1Labels = mixedMoment B raw5177step2 raw5177step2Labels := by
      have ha : raw5177step2 = (fun i j => raw5177step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5177step2 raw5177step1; decide +kernel
      have hl : raw5177step2Labels = raw5177step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5177step1 raw5177step1Labels permutation31 permutation2
    mixedMoment B raw5177step2 raw5177step2Labels = mixedMoment B raw5177step3 raw5177step3Labels := by
      have ha : raw5177step3 = -raw5177step2 := by apply Matrix.ext; change ∀ i j, raw5177step3 i j = -(raw5177step2 i j); unfold raw5177step3 raw5177step2; decide +kernel
      have hl : raw5177step3Labels = raw5177step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw5178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5178step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5178step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5178 raw5178Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw5178 raw5178Labels = mixedMoment B raw5178step0 raw5178step0Labels := by
      have hz : ∀ j, raw5178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5178step0 = (fun i j => raw5178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5178step0 raw5178; decide +kernel
      have hl : raw5178step0Labels = raw5178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5178 raw5178Labels permutation346 hz
    mixedMoment B raw5178step0 raw5178step0Labels = mixedMoment B raw5178step1 raw5178step1Labels := by
      have hz : ∀ j, raw5178step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5178step1 = (fun i j => raw5178step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5178step1 raw5178step0; decide +kernel
      have hl : raw5178step1Labels = raw5178step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5178step0 raw5178step0Labels permutation56 hz
    mixedMoment B raw5178step1 raw5178step1Labels = mixedMoment B raw5178step2 raw5178step2Labels := by
      have ha : raw5178step2 = (fun i j => raw5178step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5178step2 raw5178step1; decide +kernel
      have hl : raw5178step2Labels = raw5178step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5178step1 raw5178step1Labels permutation31 permutation2
    mixedMoment B raw5178step2 raw5178step2Labels = mixedMoment B raw5178step3 raw5178step3Labels := by
      have ha : raw5178step3 = -raw5178step2 := by apply Matrix.ext; change ∀ i j, raw5178step3 i j = -(raw5178step2 i j); unfold raw5178step3 raw5178step2; decide +kernel
      have hl : raw5178step3Labels = raw5178step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw5179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5179step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw5179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5179 raw5179Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw5179 raw5179Labels = mixedMoment B raw5179step0 raw5179step0Labels := by
      have hz : ∀ j, raw5179 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5179step0 = (fun i j => raw5179 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5179step0 raw5179; decide +kernel
      have hl : raw5179step0Labels = raw5179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5179 raw5179Labels permutation434 hz
    mixedMoment B raw5179step0 raw5179step0Labels = mixedMoment B raw5179step1 raw5179step1Labels := by
      have hz : ∀ j, raw5179step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5179step1 = (fun i j => raw5179step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5179step1 raw5179step0; decide +kernel
      have hl : raw5179step1Labels = raw5179step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5179step0 raw5179step0Labels permutation80 hz
    mixedMoment B raw5179step1 raw5179step1Labels = mixedMoment B raw5179step2 raw5179step2Labels := by
      have hz : ∀ j, raw5179step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5179step2 = (fun i j => raw5179step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5179step2 raw5179step1; decide +kernel
      have hl : raw5179step2Labels = raw5179step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5179step1 raw5179step1Labels permutation14 hz
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw5180 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5180step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5180step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5180step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5180step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5180step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5180step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5180 raw5180Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw5180 raw5180Labels = mixedMoment B raw5180step0 raw5180step0Labels := by
      have hz : ∀ j, raw5180 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5180step0 = (fun i j => raw5180 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5180step0 raw5180; decide +kernel
      have hl : raw5180step0Labels = raw5180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5180 raw5180Labels permutation434 hz
    mixedMoment B raw5180step0 raw5180step0Labels = mixedMoment B raw5180step1 raw5180step1Labels := by
      have hz : ∀ j, raw5180step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5180step1 = (fun i j => raw5180step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5180step1 raw5180step0; decide +kernel
      have hl : raw5180step1Labels = raw5180step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5180step0 raw5180step0Labels permutation80 hz
    mixedMoment B raw5180step1 raw5180step1Labels = mixedMoment B raw5180step2 raw5180step2Labels := by
      have ha : raw5180step2 = (fun i j => raw5180step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5180step2 raw5180step1; decide +kernel
      have hl : raw5180step2Labels = raw5180step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5180step1 raw5180step1Labels permutation29 permutation6
    mixedMoment B raw5180step2 raw5180step2Labels = mixedMoment B raw5180step3 raw5180step3Labels := by
      have ha : raw5180step3 = -raw5180step2 := by apply Matrix.ext; change ∀ i j, raw5180step3 i j = -(raw5180step2 i j); unfold raw5180step3 raw5180step2; decide +kernel
      have hl : raw5180step3Labels = raw5180step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5180step3 raw5180step3Labels = mixedMoment B raw5180step4 raw5180step4Labels := by
      have ha : raw5180step4 = raw5180step3 := by apply Matrix.ext; unfold raw5180step4 raw5180step3; decide +kernel
      have hl : raw5180step3Labels = labelEmbedding9 ∘ raw5180step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5180step3 raw5180step3Labels raw5180step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw5181 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5181step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5181step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5181step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5181step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5181 raw5181Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw5181 raw5181Labels = mixedMoment B raw5181step0 raw5181step0Labels := by
      have hz : ∀ j, raw5181 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5181step0 = (fun i j => raw5181 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5181step0 raw5181; decide +kernel
      have hl : raw5181step0Labels = raw5181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5181 raw5181Labels permutation434 hz
    mixedMoment B raw5181step0 raw5181step0Labels = mixedMoment B raw5181step1 raw5181step1Labels := by
      have hz : ∀ j, raw5181step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5181step1 = (fun i j => raw5181step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5181step1 raw5181step0; decide +kernel
      have hl : raw5181step1Labels = raw5181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5181step0 raw5181step0Labels permutation56 hz
    mixedMoment B raw5181step1 raw5181step1Labels = mixedMoment B raw5181step2 raw5181step2Labels := by
      have ha : raw5181step2 = (fun i j => raw5181step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5181step2 raw5181step1; decide +kernel
      have hl : raw5181step2Labels = raw5181step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5181step1 raw5181step1Labels permutation29 permutation6
    mixedMoment B raw5181step2 raw5181step2Labels = mixedMoment B raw5181step3 raw5181step3Labels := by
      have ha : raw5181step3 = -raw5181step2 := by apply Matrix.ext; change ∀ i j, raw5181step3 i j = -(raw5181step2 i j); unfold raw5181step3 raw5181step2; decide +kernel
      have hl : raw5181step3Labels = raw5181step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5181step3 raw5181step3Labels = mixedMoment B raw5181step4 raw5181step4Labels := by
      have ha : raw5181step4 = raw5181step3 := by apply Matrix.ext; unfold raw5181step4 raw5181step3; decide +kernel
      have hl : raw5181step3Labels = labelEmbedding9 ∘ raw5181step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5181step3 raw5181step3Labels raw5181step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw5182 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5182step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5182step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5182step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5182step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5182step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5182 raw5182Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw5182 raw5182Labels = mixedMoment B raw5182step0 raw5182step0Labels := by
      have hz : ∀ j, raw5182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5182step0 = (fun i j => raw5182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5182step0 raw5182; decide +kernel
      have hl : raw5182step0Labels = raw5182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5182 raw5182Labels permutation346 hz
    mixedMoment B raw5182step0 raw5182step0Labels = mixedMoment B raw5182step1 raw5182step1Labels := by
      have hz : ∀ j, raw5182step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5182step1 = (fun i j => raw5182step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5182step1 raw5182step0; decide +kernel
      have hl : raw5182step1Labels = raw5182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5182step0 raw5182step0Labels permutation56 hz
    mixedMoment B raw5182step1 raw5182step1Labels = mixedMoment B raw5182step2 raw5182step2Labels := by
      have ha : raw5182step2 = (fun i j => raw5182step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5182step2 raw5182step1; decide +kernel
      have hl : raw5182step2Labels = raw5182step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5182step1 raw5182step1Labels permutation29 permutation6
    mixedMoment B raw5182step2 raw5182step2Labels = mixedMoment B raw5182step3 raw5182step3Labels := by
      have ha : raw5182step3 = -raw5182step2 := by apply Matrix.ext; change ∀ i j, raw5182step3 i j = -(raw5182step2 i j); unfold raw5182step3 raw5182step2; decide +kernel
      have hl : raw5182step3Labels = raw5182step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5182step3 raw5182step3Labels = mixedMoment B raw5182step4 raw5182step4Labels := by
      have ha : raw5182step4 = raw5182step3 := by apply Matrix.ext; unfold raw5182step4 raw5182step3; decide +kernel
      have hl : raw5182step3Labels = labelEmbedding9 ∘ raw5182step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5182step3 raw5182step3Labels raw5182step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw5183 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5183step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5183step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, -3, 3]]
def raw5183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5183step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw5183step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5183step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw5183step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5183step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw5183step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5183 raw5183Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw5183 raw5183Labels = mixedMoment B raw5183step0 raw5183step0Labels := by
      have hz : ∀ j, raw5183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5183step0 = (fun i j => raw5183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5183step0 raw5183; decide +kernel
      have hl : raw5183step0Labels = raw5183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5183 raw5183Labels permutation434 hz
    mixedMoment B raw5183step0 raw5183step0Labels = mixedMoment B raw5183step1 raw5183step1Labels := by
      have hz : ∀ j, raw5183step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5183step1 = (fun i j => raw5183step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5183step1 raw5183step0; decide +kernel
      have hl : raw5183step1Labels = raw5183step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5183step0 raw5183step0Labels permutation80 hz
    mixedMoment B raw5183step1 raw5183step1Labels = mixedMoment B raw5183step2 raw5183step2Labels := by
      have hz : ∀ j, raw5183step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5183step2 = (fun i j => raw5183step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5183step2 raw5183step1; decide +kernel
      have hl : raw5183step2Labels = raw5183step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5183step1 raw5183step1Labels permutation14 hz
    mixedMoment B raw5183step2 raw5183step2Labels = mixedMoment B raw5183step3 raw5183step3Labels := by
      have ha : raw5183step3 = (fun i j => raw5183step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5183step3 raw5183step2; decide +kernel
      have hl : raw5183step3Labels = raw5183step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5183step2 raw5183step2Labels permutation7 permutation6
    mixedMoment B raw5183step3 raw5183step3Labels = mixedMoment B raw5183step4 raw5183step4Labels := by
      have ha : raw5183step4 = -raw5183step3 := by apply Matrix.ext; change ∀ i j, raw5183step4 i j = -(raw5183step3 i j); unfold raw5183step4 raw5183step3; decide +kernel
      have hl : raw5183step4Labels = raw5183step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5183step4 raw5183step4Labels = mixedMoment B raw5183step5 raw5183step5Labels := by
      have ha : raw5183step5 = raw5183step4 := by apply Matrix.ext; unfold raw5183step5 raw5183step4; decide +kernel
      have hl : raw5183step4Labels = labelEmbedding9 ∘ raw5183step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5183step4 raw5183step4Labels raw5183step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw5184 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw5184step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw5184step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5184 raw5184Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw5184 raw5184Labels = mixedMoment B raw5184step0 raw5184step0Labels := by
      have hz : ∀ j, raw5184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5184step0 = (fun i j => raw5184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5184step0 raw5184; decide +kernel
      have hl : raw5184step0Labels = raw5184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5184 raw5184Labels permutation434 hz
    mixedMoment B raw5184step0 raw5184step0Labels = mixedMoment B raw5184step1 raw5184step1Labels := by
      have hz : ∀ j, raw5184step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5184step1 = (fun i j => raw5184step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5184step1 raw5184step0; decide +kernel
      have hl : raw5184step1Labels = raw5184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5184step0 raw5184step0Labels permutation56 hz
    mixedMoment B raw5184step1 raw5184step1Labels = mixedMoment B raw5184step2 raw5184step2Labels := by
      have ha : raw5184step2 = (fun i j => raw5184step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5184step2 raw5184step1; decide +kernel
      have hl : raw5184step2Labels = raw5184step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5184step1 raw5184step1Labels permutation29 permutation4
    mixedMoment B raw5184step2 raw5184step2Labels = mixedMoment B raw5184step3 raw5184step3Labels := by
      have ha : raw5184step3 = raw5184step2 := by apply Matrix.ext; unfold raw5184step3 raw5184step2; decide +kernel
      have hl : raw5184step2Labels = labelEmbedding7 ∘ raw5184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5184step2 raw5184step2Labels raw5184step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4837 node4837Labels := by rfl

def raw5185 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5185step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5185step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5185 raw5185Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw5185 raw5185Labels = mixedMoment B raw5185step0 raw5185step0Labels := by
      have hz : ∀ j, raw5185 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5185step0 = (fun i j => raw5185 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5185step0 raw5185; decide +kernel
      have hl : raw5185step0Labels = raw5185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5185 raw5185Labels permutation434 hz
    mixedMoment B raw5185step0 raw5185step0Labels = mixedMoment B raw5185step1 raw5185step1Labels := by
      have ha : raw5185step1 = (fun i j => raw5185step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5185step1 raw5185step0; decide +kernel
      have hl : raw5185step1Labels = raw5185step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5185step0 raw5185step0Labels permutation143 permutation4
    mixedMoment B raw5185step1 raw5185step1Labels = mixedMoment B raw5185step2 raw5185step2Labels := by
      have ha : raw5185step2 = raw5185step1 := by apply Matrix.ext; unfold raw5185step2 raw5185step1; decide +kernel
      have hl : raw5185step1Labels = labelEmbedding7 ∘ raw5185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5185step1 raw5185step1Labels raw5185step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw5186 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5186step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5186step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5186 raw5186Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw5186 raw5186Labels = mixedMoment B raw5186step0 raw5186step0Labels := by
      have hz : ∀ j, raw5186 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5186step0 = (fun i j => raw5186 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5186step0 raw5186; decide +kernel
      have hl : raw5186step0Labels = raw5186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5186 raw5186Labels permutation265 hz
    mixedMoment B raw5186step0 raw5186step0Labels = mixedMoment B raw5186step1 raw5186step1Labels := by
      have ha : raw5186step1 = (fun i j => raw5186step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5186step1 raw5186step0; decide +kernel
      have hl : raw5186step1Labels = raw5186step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5186step0 raw5186step0Labels permutation137 permutation4
    mixedMoment B raw5186step1 raw5186step1Labels = mixedMoment B raw5186step2 raw5186step2Labels := by
      have ha : raw5186step2 = raw5186step1 := by apply Matrix.ext; unfold raw5186step2 raw5186step1; decide +kernel
      have hl : raw5186step1Labels = labelEmbedding7 ∘ raw5186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5186step1 raw5186step1Labels raw5186step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw5187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw5187step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5187step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw5187step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5187 raw5187Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw5187 raw5187Labels = mixedMoment B raw5187step0 raw5187step0Labels := by
      have hz : ∀ j, raw5187 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5187step0 = (fun i j => raw5187 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5187step0 raw5187; decide +kernel
      have hl : raw5187step0Labels = raw5187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5187 raw5187Labels permutation434 hz
    mixedMoment B raw5187step0 raw5187step0Labels = mixedMoment B raw5187step1 raw5187step1Labels := by
      have hz : ∀ j, raw5187step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5187step1 = (fun i j => raw5187step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5187step1 raw5187step0; decide +kernel
      have hl : raw5187step1Labels = raw5187step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5187step0 raw5187step0Labels permutation56 hz
    mixedMoment B raw5187step1 raw5187step1Labels = mixedMoment B raw5187step2 raw5187step2Labels := by
      have ha : raw5187step2 = (fun i j => raw5187step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5187step2 raw5187step1; decide +kernel
      have hl : raw5187step2Labels = raw5187step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5187step1 raw5187step1Labels permutation29 permutation4
    mixedMoment B raw5187step2 raw5187step2Labels = mixedMoment B raw5187step3 raw5187step3Labels := by
      have ha : raw5187step3 = raw5187step2 := by apply Matrix.ext; unfold raw5187step3 raw5187step2; decide +kernel
      have hl : raw5187step2Labels = labelEmbedding7 ∘ raw5187step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5187step2 raw5187step2Labels raw5187step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw5188 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5188step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw5188step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5188step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw5188step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5188 raw5188Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw5188 raw5188Labels = mixedMoment B raw5188step0 raw5188step0Labels := by
      have hz : ∀ j, raw5188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5188step0 = (fun i j => raw5188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5188step0 raw5188; decide +kernel
      have hl : raw5188step0Labels = raw5188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5188 raw5188Labels permutation346 hz
    mixedMoment B raw5188step0 raw5188step0Labels = mixedMoment B raw5188step1 raw5188step1Labels := by
      have hz : ∀ j, raw5188step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5188step1 = (fun i j => raw5188step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5188step1 raw5188step0; decide +kernel
      have hl : raw5188step1Labels = raw5188step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5188step0 raw5188step0Labels permutation56 hz
    mixedMoment B raw5188step1 raw5188step1Labels = mixedMoment B raw5188step2 raw5188step2Labels := by
      have ha : raw5188step2 = (fun i j => raw5188step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5188step2 raw5188step1; decide +kernel
      have hl : raw5188step2Labels = raw5188step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5188step1 raw5188step1Labels permutation29 permutation4
    mixedMoment B raw5188step2 raw5188step2Labels = mixedMoment B raw5188step3 raw5188step3Labels := by
      have ha : raw5188step3 = raw5188step2 := by apply Matrix.ext; unfold raw5188step3 raw5188step2; decide +kernel
      have hl : raw5188step2Labels = labelEmbedding7 ∘ raw5188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5188step2 raw5188step2Labels raw5188step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4837 node4837Labels := by rfl

def raw5189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5189step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5189 raw5189Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw5189 raw5189Labels = mixedMoment B raw5189step0 raw5189step0Labels := by
      have hz : ∀ j, raw5189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5189step0 = (fun i j => raw5189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5189step0 raw5189; decide +kernel
      have hl : raw5189step0Labels = raw5189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5189 raw5189Labels permutation346 hz
    mixedMoment B raw5189step0 raw5189step0Labels = mixedMoment B raw5189step1 raw5189step1Labels := by
      have ha : raw5189step1 = (fun i j => raw5189step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5189step1 raw5189step0; decide +kernel
      have hl : raw5189step1Labels = raw5189step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5189step0 raw5189step0Labels permutation143 permutation4
    mixedMoment B raw5189step1 raw5189step1Labels = mixedMoment B raw5189step2 raw5189step2Labels := by
      have ha : raw5189step2 = raw5189step1 := by apply Matrix.ext; unfold raw5189step2 raw5189step1; decide +kernel
      have hl : raw5189step1Labels = labelEmbedding7 ∘ raw5189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5189step1 raw5189step1Labels raw5189step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw5190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5190step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5190 raw5190Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw5190 raw5190Labels = mixedMoment B raw5190step0 raw5190step0Labels := by
      have hz : ∀ j, raw5190 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5190step0 = (fun i j => raw5190 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5190step0 raw5190; decide +kernel
      have hl : raw5190step0Labels = raw5190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5190 raw5190Labels permutation265 hz
    mixedMoment B raw5190step0 raw5190step0Labels = mixedMoment B raw5190step1 raw5190step1Labels := by
      have ha : raw5190step1 = (fun i j => raw5190step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5190step1 raw5190step0; decide +kernel
      have hl : raw5190step1Labels = raw5190step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5190step0 raw5190step0Labels permutation143 permutation4
    mixedMoment B raw5190step1 raw5190step1Labels = mixedMoment B raw5190step2 raw5190step2Labels := by
      have ha : raw5190step2 = raw5190step1 := by apply Matrix.ext; unfold raw5190step2 raw5190step1; decide +kernel
      have hl : raw5190step1Labels = labelEmbedding7 ∘ raw5190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5190step1 raw5190step1Labels raw5190step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw5191 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5191step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5191step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw5191step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5191step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw5191step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5191 raw5191Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw5191 raw5191Labels = mixedMoment B raw5191step0 raw5191step0Labels := by
      have hz : ∀ j, raw5191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5191step0 = (fun i j => raw5191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5191step0 raw5191; decide +kernel
      have hl : raw5191step0Labels = raw5191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5191 raw5191Labels permutation346 hz
    mixedMoment B raw5191step0 raw5191step0Labels = mixedMoment B raw5191step1 raw5191step1Labels := by
      have hz : ∀ j, raw5191step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5191step1 = (fun i j => raw5191step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5191step1 raw5191step0; decide +kernel
      have hl : raw5191step1Labels = raw5191step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5191step0 raw5191step0Labels permutation56 hz
    mixedMoment B raw5191step1 raw5191step1Labels = mixedMoment B raw5191step2 raw5191step2Labels := by
      have ha : raw5191step2 = (fun i j => raw5191step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5191step2 raw5191step1; decide +kernel
      have hl : raw5191step2Labels = raw5191step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5191step1 raw5191step1Labels permutation29 permutation4
    mixedMoment B raw5191step2 raw5191step2Labels = mixedMoment B raw5191step3 raw5191step3Labels := by
      have ha : raw5191step3 = raw5191step2 := by apply Matrix.ext; unfold raw5191step3 raw5191step2; decide +kernel
      have hl : raw5191step2Labels = labelEmbedding7 ∘ raw5191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5191step2 raw5191step2Labels raw5191step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw5192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5192step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5192step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -4, 3]]
def raw5192step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5192step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw5192step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5192step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw5192step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5192 raw5192Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw5192 raw5192Labels = mixedMoment B raw5192step0 raw5192step0Labels := by
      have hz : ∀ j, raw5192 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5192step0 = (fun i j => raw5192 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5192step0 raw5192; decide +kernel
      have hl : raw5192step0Labels = raw5192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5192 raw5192Labels permutation434 hz
    mixedMoment B raw5192step0 raw5192step0Labels = mixedMoment B raw5192step1 raw5192step1Labels := by
      have hz : ∀ j, raw5192step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5192step1 = (fun i j => raw5192step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5192step1 raw5192step0; decide +kernel
      have hl : raw5192step1Labels = raw5192step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5192step0 raw5192step0Labels permutation80 hz
    mixedMoment B raw5192step1 raw5192step1Labels = mixedMoment B raw5192step2 raw5192step2Labels := by
      have hz : ∀ j, raw5192step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5192step2 = (fun i j => raw5192step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5192step2 raw5192step1; decide +kernel
      have hl : raw5192step2Labels = raw5192step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5192step1 raw5192step1Labels permutation14 hz
    mixedMoment B raw5192step2 raw5192step2Labels = mixedMoment B raw5192step3 raw5192step3Labels := by
      have ha : raw5192step3 = (fun i j => raw5192step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5192step3 raw5192step2; decide +kernel
      have hl : raw5192step3Labels = raw5192step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5192step2 raw5192step2Labels permutation7 permutation4
    mixedMoment B raw5192step3 raw5192step3Labels = mixedMoment B raw5192step4 raw5192step4Labels := by
      have ha : raw5192step4 = raw5192step3 := by apply Matrix.ext; unfold raw5192step4 raw5192step3; decide +kernel
      have hl : raw5192step3Labels = labelEmbedding7 ∘ raw5192step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5192step3 raw5192step3Labels raw5192step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw5193 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5193step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5193step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5193step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5193step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5193step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5193 raw5193Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw5193 raw5193Labels = mixedMoment B raw5193step0 raw5193step0Labels := by
      have hz : ∀ j, raw5193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5193step0 = (fun i j => raw5193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5193step0 raw5193; decide +kernel
      have hl : raw5193step0Labels = raw5193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5193 raw5193Labels permutation434 hz
    mixedMoment B raw5193step0 raw5193step0Labels = mixedMoment B raw5193step1 raw5193step1Labels := by
      have hz : ∀ j, raw5193step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5193step1 = (fun i j => raw5193step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5193step1 raw5193step0; decide +kernel
      have hl : raw5193step1Labels = raw5193step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5193step0 raw5193step0Labels permutation80 hz
    mixedMoment B raw5193step1 raw5193step1Labels = mixedMoment B raw5193step2 raw5193step2Labels := by
      have ha : raw5193step2 = (fun i j => raw5193step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5193step2 raw5193step1; decide +kernel
      have hl : raw5193step2Labels = raw5193step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5193step1 raw5193step1Labels permutation29 permutation4
    mixedMoment B raw5193step2 raw5193step2Labels = mixedMoment B raw5193step3 raw5193step3Labels := by
      have ha : raw5193step3 = raw5193step2 := by apply Matrix.ext; unfold raw5193step3 raw5193step2; decide +kernel
      have hl : raw5193step2Labels = labelEmbedding7 ∘ raw5193step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5193step2 raw5193step2Labels raw5193step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw5194 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5194step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5194step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5194step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5194 raw5194Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw5194 raw5194Labels = mixedMoment B raw5194step0 raw5194step0Labels := by
      have hz : ∀ j, raw5194 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5194step0 = (fun i j => raw5194 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5194step0 raw5194; decide +kernel
      have hl : raw5194step0Labels = raw5194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5194 raw5194Labels permutation434 hz
    mixedMoment B raw5194step0 raw5194step0Labels = mixedMoment B raw5194step1 raw5194step1Labels := by
      have hz : ∀ j, raw5194step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5194step1 = (fun i j => raw5194step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5194step1 raw5194step0; decide +kernel
      have hl : raw5194step1Labels = raw5194step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5194step0 raw5194step0Labels permutation56 hz
    mixedMoment B raw5194step1 raw5194step1Labels = mixedMoment B raw5194step2 raw5194step2Labels := by
      have ha : raw5194step2 = (fun i j => raw5194step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5194step2 raw5194step1; decide +kernel
      have hl : raw5194step2Labels = raw5194step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5194step1 raw5194step1Labels permutation29 permutation4
    mixedMoment B raw5194step2 raw5194step2Labels = mixedMoment B raw5194step3 raw5194step3Labels := by
      have ha : raw5194step3 = raw5194step2 := by apply Matrix.ext; unfold raw5194step3 raw5194step2; decide +kernel
      have hl : raw5194step2Labels = labelEmbedding7 ∘ raw5194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5194step2 raw5194step2Labels raw5194step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw5195 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5195step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5195step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5195step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5195 raw5195Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw5195 raw5195Labels = mixedMoment B raw5195step0 raw5195step0Labels := by
      have hz : ∀ j, raw5195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5195step0 = (fun i j => raw5195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5195step0 raw5195; decide +kernel
      have hl : raw5195step0Labels = raw5195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5195 raw5195Labels permutation346 hz
    mixedMoment B raw5195step0 raw5195step0Labels = mixedMoment B raw5195step1 raw5195step1Labels := by
      have hz : ∀ j, raw5195step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5195step1 = (fun i j => raw5195step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5195step1 raw5195step0; decide +kernel
      have hl : raw5195step1Labels = raw5195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5195step0 raw5195step0Labels permutation56 hz
    mixedMoment B raw5195step1 raw5195step1Labels = mixedMoment B raw5195step2 raw5195step2Labels := by
      have ha : raw5195step2 = (fun i j => raw5195step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5195step2 raw5195step1; decide +kernel
      have hl : raw5195step2Labels = raw5195step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5195step1 raw5195step1Labels permutation29 permutation4
    mixedMoment B raw5195step2 raw5195step2Labels = mixedMoment B raw5195step3 raw5195step3Labels := by
      have ha : raw5195step3 = raw5195step2 := by apply Matrix.ext; unfold raw5195step3 raw5195step2; decide +kernel
      have hl : raw5195step2Labels = labelEmbedding7 ∘ raw5195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5195step2 raw5195step2Labels raw5195step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw5196 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -4, 3]]
def raw5196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -4, 3]]
def raw5196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -4, 3]]
def raw5196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5196step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -4, 3]]
def raw5196step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5196step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw5196step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5196step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw5196step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5196 raw5196Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw5196 raw5196Labels = mixedMoment B raw5196step0 raw5196step0Labels := by
      have hz : ∀ j, raw5196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5196step0 = (fun i j => raw5196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5196step0 raw5196; decide +kernel
      have hl : raw5196step0Labels = raw5196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5196 raw5196Labels permutation434 hz
    mixedMoment B raw5196step0 raw5196step0Labels = mixedMoment B raw5196step1 raw5196step1Labels := by
      have hz : ∀ j, raw5196step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5196step1 = (fun i j => raw5196step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5196step1 raw5196step0; decide +kernel
      have hl : raw5196step1Labels = raw5196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5196step0 raw5196step0Labels permutation80 hz
    mixedMoment B raw5196step1 raw5196step1Labels = mixedMoment B raw5196step2 raw5196step2Labels := by
      have hz : ∀ j, raw5196step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5196step2 = (fun i j => raw5196step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5196step2 raw5196step1; decide +kernel
      have hl : raw5196step2Labels = raw5196step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5196step1 raw5196step1Labels permutation14 hz
    mixedMoment B raw5196step2 raw5196step2Labels = mixedMoment B raw5196step3 raw5196step3Labels := by
      have ha : raw5196step3 = (fun i j => raw5196step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5196step3 raw5196step2; decide +kernel
      have hl : raw5196step3Labels = raw5196step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5196step2 raw5196step2Labels permutation7 permutation4
    mixedMoment B raw5196step3 raw5196step3Labels = mixedMoment B raw5196step4 raw5196step4Labels := by
      have ha : raw5196step4 = raw5196step3 := by apply Matrix.ext; unfold raw5196step4 raw5196step3; decide +kernel
      have hl : raw5196step3Labels = labelEmbedding7 ∘ raw5196step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5196step3 raw5196step3Labels raw5196step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw5197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5197Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5197step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5197step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5197step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5197step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5197step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5197step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5197 raw5197Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5197 raw5197Labels = mixedMoment B raw5197step0 raw5197step0Labels := by
      have hz : ∀ j, raw5197 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5197step0 = (fun i j => raw5197 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5197step0 raw5197; decide +kernel
      have hl : raw5197step0Labels = raw5197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197 raw5197Labels permutation520 hz
    mixedMoment B raw5197step0 raw5197step0Labels = mixedMoment B raw5197step1 raw5197step1Labels := by
      have hz : ∀ j, raw5197step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5197step1 = (fun i j => raw5197step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5197step1 raw5197step0; decide +kernel
      have hl : raw5197step1Labels = raw5197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197step0 raw5197step0Labels permutation104 hz
    mixedMoment B raw5197step1 raw5197step1Labels = mixedMoment B raw5197step2 raw5197step2Labels := by
      have hz : ∀ j, raw5197step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5197step2 = (fun i j => raw5197step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5197step2 raw5197step1; decide +kernel
      have hl : raw5197step2Labels = raw5197step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5197step1 raw5197step1Labels permutation20 hz
    mixedMoment B raw5197step2 raw5197step2Labels = mixedMoment B raw5197step3 raw5197step3Labels := by
      have hz : ∀ i, raw5197step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5197step3 = (fun i j => raw5197step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5197step3 raw5197step2; decide +kernel
      have hl : raw5197step3Labels = (fun j => raw5197step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5197step2 raw5197step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw5198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5198Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5198step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5198step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5198step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5198step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5198step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5198step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5198 raw5198Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5198 raw5198Labels = mixedMoment B raw5198step0 raw5198step0Labels := by
      have hz : ∀ j, raw5198 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5198step0 = (fun i j => raw5198 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5198step0 raw5198; decide +kernel
      have hl : raw5198step0Labels = raw5198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5198 raw5198Labels permutation520 hz
    mixedMoment B raw5198step0 raw5198step0Labels = mixedMoment B raw5198step1 raw5198step1Labels := by
      have hz : ∀ j, raw5198step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5198step1 = (fun i j => raw5198step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5198step1 raw5198step0; decide +kernel
      have hl : raw5198step1Labels = raw5198step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5198step0 raw5198step0Labels permutation104 hz
    mixedMoment B raw5198step1 raw5198step1Labels = mixedMoment B raw5198step2 raw5198step2Labels := by
      have hz : ∀ i, raw5198step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5198step2 = (fun i j => raw5198step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5198step2 raw5198step1; decide +kernel
      have hl : raw5198step2Labels = (fun j => raw5198step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5198step1 raw5198step1Labels permutation6 hz
    mixedMoment B raw5198step2 raw5198step2Labels = mixedMoment B raw5198step3 raw5198step3Labels := by
      have ha : raw5198step3 = (fun i j => raw5198step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5198step3 raw5198step2; decide +kernel
      have hl : raw5198step3Labels = raw5198step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5198step2 raw5198step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5199Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5199step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5199step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5199step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5199step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5199step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5199step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5199 raw5199Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5199 raw5199Labels = mixedMoment B raw5199step0 raw5199step0Labels := by
      have hz : ∀ j, raw5199 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5199step0 = (fun i j => raw5199 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5199step0 raw5199; decide +kernel
      have hl : raw5199step0Labels = raw5199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5199 raw5199Labels permutation520 hz
    mixedMoment B raw5199step0 raw5199step0Labels = mixedMoment B raw5199step1 raw5199step1Labels := by
      have hz : ∀ j, raw5199step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5199step1 = (fun i j => raw5199step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5199step1 raw5199step0; decide +kernel
      have hl : raw5199step1Labels = raw5199step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5199step0 raw5199step0Labels permutation80 hz
    mixedMoment B raw5199step1 raw5199step1Labels = mixedMoment B raw5199step2 raw5199step2Labels := by
      have hz : ∀ i, raw5199step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5199step2 = (fun i j => raw5199step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5199step2 raw5199step1; decide +kernel
      have hl : raw5199step2Labels = (fun j => raw5199step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5199step1 raw5199step1Labels permutation6 hz
    mixedMoment B raw5199step2 raw5199step2Labels = mixedMoment B raw5199step3 raw5199step3Labels := by
      have ha : raw5199step3 = (fun i j => raw5199step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5199step3 raw5199step2; decide +kernel
      have hl : raw5199step3Labels = raw5199step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5199step2 raw5199step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5200Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5200step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5200step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5200step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5200step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5200step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5200step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5200 raw5200Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5200 raw5200Labels = mixedMoment B raw5200step0 raw5200step0Labels := by
      have hz : ∀ j, raw5200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5200step0 = (fun i j => raw5200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5200step0 raw5200; decide +kernel
      have hl : raw5200step0Labels = raw5200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5200 raw5200Labels permutation434 hz
    mixedMoment B raw5200step0 raw5200step0Labels = mixedMoment B raw5200step1 raw5200step1Labels := by
      have hz : ∀ j, raw5200step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5200step1 = (fun i j => raw5200step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5200step1 raw5200step0; decide +kernel
      have hl : raw5200step1Labels = raw5200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5200step0 raw5200step0Labels permutation80 hz
    mixedMoment B raw5200step1 raw5200step1Labels = mixedMoment B raw5200step2 raw5200step2Labels := by
      have hz : ∀ i, raw5200step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5200step2 = (fun i j => raw5200step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5200step2 raw5200step1; decide +kernel
      have hl : raw5200step2Labels = (fun j => raw5200step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5200step1 raw5200step1Labels permutation6 hz
    mixedMoment B raw5200step2 raw5200step2Labels = mixedMoment B raw5200step3 raw5200step3Labels := by
      have ha : raw5200step3 = (fun i j => raw5200step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5200step3 raw5200step2; decide +kernel
      have hl : raw5200step3Labels = raw5200step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5200step2 raw5200step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5201Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5201step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5201step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5201step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5201step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5201step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5201step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5201 raw5201Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5201 raw5201Labels = mixedMoment B raw5201step0 raw5201step0Labels := by
      have hz : ∀ j, raw5201 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5201step0 = (fun i j => raw5201 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5201step0 raw5201; decide +kernel
      have hl : raw5201step0Labels = raw5201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201 raw5201Labels permutation520 hz
    mixedMoment B raw5201step0 raw5201step0Labels = mixedMoment B raw5201step1 raw5201step1Labels := by
      have hz : ∀ j, raw5201step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5201step1 = (fun i j => raw5201step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5201step1 raw5201step0; decide +kernel
      have hl : raw5201step1Labels = raw5201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201step0 raw5201step0Labels permutation104 hz
    mixedMoment B raw5201step1 raw5201step1Labels = mixedMoment B raw5201step2 raw5201step2Labels := by
      have hz : ∀ j, raw5201step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5201step2 = (fun i j => raw5201step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5201step2 raw5201step1; decide +kernel
      have hl : raw5201step2Labels = raw5201step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5201step1 raw5201step1Labels permutation14 hz
    mixedMoment B raw5201step2 raw5201step2Labels = mixedMoment B raw5201step3 raw5201step3Labels := by
      have hz : ∀ i, raw5201step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5201step3 = (fun i j => raw5201step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5201step3 raw5201step2; decide +kernel
      have hl : raw5201step3Labels = (fun j => raw5201step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5201step2 raw5201step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw5202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5202Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5202step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5202step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5202step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5202step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5202 raw5202Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5202 raw5202Labels = mixedMoment B raw5202step0 raw5202step0Labels := by
      have hz : ∀ j, raw5202 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5202step0 = (fun i j => raw5202 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5202step0 raw5202; decide +kernel
      have hl : raw5202step0Labels = raw5202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5202 raw5202Labels permutation520 hz
    mixedMoment B raw5202step0 raw5202step0Labels = mixedMoment B raw5202step1 raw5202step1Labels := by
      have hz : ∀ j, raw5202step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5202step1 = (fun i j => raw5202step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5202step1 raw5202step0; decide +kernel
      have hl : raw5202step1Labels = raw5202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5202step0 raw5202step0Labels permutation104 hz
    mixedMoment B raw5202step1 raw5202step1Labels = mixedMoment B raw5202step2 raw5202step2Labels := by
      have hz : ∀ i, raw5202step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5202step2 = (fun i j => raw5202step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5202step2 raw5202step1; decide +kernel
      have hl : raw5202step2Labels = (fun j => raw5202step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5202step1 raw5202step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5203Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5203step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5203step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5203step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5203step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5203step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5203step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5203 raw5203Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5203 raw5203Labels = mixedMoment B raw5203step0 raw5203step0Labels := by
      have hz : ∀ j, raw5203 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5203step0 = (fun i j => raw5203 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5203step0 raw5203; decide +kernel
      have hl : raw5203step0Labels = raw5203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5203 raw5203Labels permutation520 hz
    mixedMoment B raw5203step0 raw5203step0Labels = mixedMoment B raw5203step1 raw5203step1Labels := by
      have hz : ∀ j, raw5203step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5203step1 = (fun i j => raw5203step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5203step1 raw5203step0; decide +kernel
      have hl : raw5203step1Labels = raw5203step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5203step0 raw5203step0Labels permutation56 hz
    mixedMoment B raw5203step1 raw5203step1Labels = mixedMoment B raw5203step2 raw5203step2Labels := by
      have hz : ∀ i, raw5203step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5203step2 = (fun i j => raw5203step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5203step2 raw5203step1; decide +kernel
      have hl : raw5203step2Labels = (fun j => raw5203step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5203step1 raw5203step1Labels permutation6 hz
    mixedMoment B raw5203step2 raw5203step2Labels = mixedMoment B raw5203step3 raw5203step3Labels := by
      have ha : raw5203step3 = (fun i j => raw5203step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5203step3 raw5203step2; decide +kernel
      have hl : raw5203step3Labels = raw5203step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5203step2 raw5203step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5204Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5204step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5204step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5204step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5204step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5204step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5204step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5204 raw5204Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5204 raw5204Labels = mixedMoment B raw5204step0 raw5204step0Labels := by
      have hz : ∀ j, raw5204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5204step0 = (fun i j => raw5204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5204step0 raw5204; decide +kernel
      have hl : raw5204step0Labels = raw5204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5204 raw5204Labels permutation434 hz
    mixedMoment B raw5204step0 raw5204step0Labels = mixedMoment B raw5204step1 raw5204step1Labels := by
      have hz : ∀ j, raw5204step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5204step1 = (fun i j => raw5204step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5204step1 raw5204step0; decide +kernel
      have hl : raw5204step1Labels = raw5204step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5204step0 raw5204step0Labels permutation56 hz
    mixedMoment B raw5204step1 raw5204step1Labels = mixedMoment B raw5204step2 raw5204step2Labels := by
      have hz : ∀ i, raw5204step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5204step2 = (fun i j => raw5204step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5204step2 raw5204step1; decide +kernel
      have hl : raw5204step2Labels = (fun j => raw5204step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5204step1 raw5204step1Labels permutation6 hz
    mixedMoment B raw5204step2 raw5204step2Labels = mixedMoment B raw5204step3 raw5204step3Labels := by
      have ha : raw5204step3 = (fun i j => raw5204step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5204step3 raw5204step2; decide +kernel
      have hl : raw5204step3Labels = raw5204step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5204step2 raw5204step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5205Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5205step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5205step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5205step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5205step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5205step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5205step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5205 raw5205Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5205 raw5205Labels = mixedMoment B raw5205step0 raw5205step0Labels := by
      have hz : ∀ j, raw5205 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5205step0 = (fun i j => raw5205 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5205step0 raw5205; decide +kernel
      have hl : raw5205step0Labels = raw5205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205 raw5205Labels permutation520 hz
    mixedMoment B raw5205step0 raw5205step0Labels = mixedMoment B raw5205step1 raw5205step1Labels := by
      have hz : ∀ j, raw5205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5205step1 = (fun i j => raw5205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5205step1 raw5205step0; decide +kernel
      have hl : raw5205step1Labels = raw5205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205step0 raw5205step0Labels permutation80 hz
    mixedMoment B raw5205step1 raw5205step1Labels = mixedMoment B raw5205step2 raw5205step2Labels := by
      have hz : ∀ j, raw5205step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5205step2 = (fun i j => raw5205step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5205step2 raw5205step1; decide +kernel
      have hl : raw5205step2Labels = raw5205step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5205step1 raw5205step1Labels permutation14 hz
    mixedMoment B raw5205step2 raw5205step2Labels = mixedMoment B raw5205step3 raw5205step3Labels := by
      have hz : ∀ i, raw5205step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5205step3 = (fun i j => raw5205step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5205step3 raw5205step2; decide +kernel
      have hl : raw5205step3Labels = (fun j => raw5205step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5205step2 raw5205step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw5206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5206Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5206step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5206step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5206step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5206step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5206 raw5206Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5206 raw5206Labels = mixedMoment B raw5206step0 raw5206step0Labels := by
      have hz : ∀ j, raw5206 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5206step0 = (fun i j => raw5206 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5206step0 raw5206; decide +kernel
      have hl : raw5206step0Labels = raw5206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5206 raw5206Labels permutation520 hz
    mixedMoment B raw5206step0 raw5206step0Labels = mixedMoment B raw5206step1 raw5206step1Labels := by
      have hz : ∀ j, raw5206step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5206step1 = (fun i j => raw5206step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5206step1 raw5206step0; decide +kernel
      have hl : raw5206step1Labels = raw5206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5206step0 raw5206step0Labels permutation80 hz
    mixedMoment B raw5206step1 raw5206step1Labels = mixedMoment B raw5206step2 raw5206step2Labels := by
      have hz : ∀ i, raw5206step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5206step2 = (fun i j => raw5206step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5206step2 raw5206step1; decide +kernel
      have hl : raw5206step2Labels = (fun j => raw5206step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5206step1 raw5206step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5207Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5207step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5207step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5207step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5207step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5207 raw5207Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5207 raw5207Labels = mixedMoment B raw5207step0 raw5207step0Labels := by
      have hz : ∀ j, raw5207 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5207step0 = (fun i j => raw5207 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5207step0 raw5207; decide +kernel
      have hl : raw5207step0Labels = raw5207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5207 raw5207Labels permutation520 hz
    mixedMoment B raw5207step0 raw5207step0Labels = mixedMoment B raw5207step1 raw5207step1Labels := by
      have hz : ∀ j, raw5207step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5207step1 = (fun i j => raw5207step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5207step1 raw5207step0; decide +kernel
      have hl : raw5207step1Labels = raw5207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5207step0 raw5207step0Labels permutation56 hz
    mixedMoment B raw5207step1 raw5207step1Labels = mixedMoment B raw5207step2 raw5207step2Labels := by
      have hz : ∀ i, raw5207step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5207step2 = (fun i j => raw5207step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5207step2 raw5207step1; decide +kernel
      have hl : raw5207step2Labels = (fun j => raw5207step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5207step1 raw5207step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5208Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5208step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5208step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5208step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5208step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5208step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5208step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5208 raw5208Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5208 raw5208Labels = mixedMoment B raw5208step0 raw5208step0Labels := by
      have hz : ∀ j, raw5208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5208step0 = (fun i j => raw5208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5208step0 raw5208; decide +kernel
      have hl : raw5208step0Labels = raw5208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5208 raw5208Labels permutation346 hz
    mixedMoment B raw5208step0 raw5208step0Labels = mixedMoment B raw5208step1 raw5208step1Labels := by
      have hz : ∀ j, raw5208step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5208step1 = (fun i j => raw5208step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5208step1 raw5208step0; decide +kernel
      have hl : raw5208step1Labels = raw5208step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5208step0 raw5208step0Labels permutation56 hz
    mixedMoment B raw5208step1 raw5208step1Labels = mixedMoment B raw5208step2 raw5208step2Labels := by
      have hz : ∀ i, raw5208step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5208step2 = (fun i j => raw5208step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5208step2 raw5208step1; decide +kernel
      have hl : raw5208step2Labels = (fun j => raw5208step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5208step1 raw5208step1Labels permutation6 hz
    mixedMoment B raw5208step2 raw5208step2Labels = mixedMoment B raw5208step3 raw5208step3Labels := by
      have ha : raw5208step3 = (fun i j => raw5208step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5208step3 raw5208step2; decide +kernel
      have hl : raw5208step3Labels = raw5208step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5208step2 raw5208step2Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5209Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5209step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5209step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5209step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5209step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5209step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5209step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5209 raw5209Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5209 raw5209Labels = mixedMoment B raw5209step0 raw5209step0Labels := by
      have hz : ∀ j, raw5209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5209step0 = (fun i j => raw5209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5209step0 raw5209; decide +kernel
      have hl : raw5209step0Labels = raw5209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209 raw5209Labels permutation434 hz
    mixedMoment B raw5209step0 raw5209step0Labels = mixedMoment B raw5209step1 raw5209step1Labels := by
      have hz : ∀ j, raw5209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5209step1 = (fun i j => raw5209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5209step1 raw5209step0; decide +kernel
      have hl : raw5209step1Labels = raw5209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209step0 raw5209step0Labels permutation80 hz
    mixedMoment B raw5209step1 raw5209step1Labels = mixedMoment B raw5209step2 raw5209step2Labels := by
      have hz : ∀ j, raw5209step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5209step2 = (fun i j => raw5209step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5209step2 raw5209step1; decide +kernel
      have hl : raw5209step2Labels = raw5209step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209step1 raw5209step1Labels permutation14 hz
    mixedMoment B raw5209step2 raw5209step2Labels = mixedMoment B raw5209step3 raw5209step3Labels := by
      have hz : ∀ i, raw5209step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5209step3 = (fun i j => raw5209step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5209step3 raw5209step2; decide +kernel
      have hl : raw5209step3Labels = (fun j => raw5209step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5209step2 raw5209step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw5210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5210Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5210step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5210step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5210step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5210step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5210 raw5210Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5210 raw5210Labels = mixedMoment B raw5210step0 raw5210step0Labels := by
      have hz : ∀ j, raw5210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5210step0 = (fun i j => raw5210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5210step0 raw5210; decide +kernel
      have hl : raw5210step0Labels = raw5210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5210 raw5210Labels permutation434 hz
    mixedMoment B raw5210step0 raw5210step0Labels = mixedMoment B raw5210step1 raw5210step1Labels := by
      have hz : ∀ j, raw5210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5210step1 = (fun i j => raw5210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5210step1 raw5210step0; decide +kernel
      have hl : raw5210step1Labels = raw5210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5210step0 raw5210step0Labels permutation80 hz
    mixedMoment B raw5210step1 raw5210step1Labels = mixedMoment B raw5210step2 raw5210step2Labels := by
      have hz : ∀ i, raw5210step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5210step2 = (fun i j => raw5210step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5210step2 raw5210step1; decide +kernel
      have hl : raw5210step2Labels = (fun j => raw5210step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5210step1 raw5210step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5211Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5211step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5211step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5211step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5211step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5211 raw5211Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5211 raw5211Labels = mixedMoment B raw5211step0 raw5211step0Labels := by
      have hz : ∀ j, raw5211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5211step0 = (fun i j => raw5211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5211step0 raw5211; decide +kernel
      have hl : raw5211step0Labels = raw5211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5211 raw5211Labels permutation434 hz
    mixedMoment B raw5211step0 raw5211step0Labels = mixedMoment B raw5211step1 raw5211step1Labels := by
      have hz : ∀ j, raw5211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5211step1 = (fun i j => raw5211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5211step1 raw5211step0; decide +kernel
      have hl : raw5211step1Labels = raw5211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5211step0 raw5211step0Labels permutation56 hz
    mixedMoment B raw5211step1 raw5211step1Labels = mixedMoment B raw5211step2 raw5211step2Labels := by
      have hz : ∀ i, raw5211step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5211step2 = (fun i j => raw5211step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5211step2 raw5211step1; decide +kernel
      have hl : raw5211step2Labels = (fun j => raw5211step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5211step1 raw5211step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5212Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5212step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5212step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5212step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5212step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5212 raw5212Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5212 raw5212Labels = mixedMoment B raw5212step0 raw5212step0Labels := by
      have hz : ∀ j, raw5212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5212step0 = (fun i j => raw5212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5212step0 raw5212; decide +kernel
      have hl : raw5212step0Labels = raw5212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5212 raw5212Labels permutation346 hz
    mixedMoment B raw5212step0 raw5212step0Labels = mixedMoment B raw5212step1 raw5212step1Labels := by
      have hz : ∀ j, raw5212step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5212step1 = (fun i j => raw5212step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5212step1 raw5212step0; decide +kernel
      have hl : raw5212step1Labels = raw5212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5212step0 raw5212step0Labels permutation56 hz
    mixedMoment B raw5212step1 raw5212step1Labels = mixedMoment B raw5212step2 raw5212step2Labels := by
      have hz : ∀ i, raw5212step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5212step2 = (fun i j => raw5212step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5212step2 raw5212step1; decide +kernel
      have hl : raw5212step2Labels = (fun j => raw5212step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5212step1 raw5212step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw5213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5213Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5213step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5213step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5213step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5213step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5213step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 4, 0], ![4, -4, 0]]
def raw5213step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5213step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]
def raw5213step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5213 raw5213Labels = mixedMoment B node4072 node4072Labels := by
  calc
    mixedMoment B raw5213 raw5213Labels = mixedMoment B raw5213step0 raw5213step0Labels := by
      have hz : ∀ j, raw5213 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5213step0 = (fun i j => raw5213 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5213step0 raw5213; decide +kernel
      have hl : raw5213step0Labels = raw5213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213 raw5213Labels permutation520 hz
    mixedMoment B raw5213step0 raw5213step0Labels = mixedMoment B raw5213step1 raw5213step1Labels := by
      have hz : ∀ j, raw5213step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5213step1 = (fun i j => raw5213step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5213step1 raw5213step0; decide +kernel
      have hl : raw5213step1Labels = raw5213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213step0 raw5213step0Labels permutation104 hz
    mixedMoment B raw5213step1 raw5213step1Labels = mixedMoment B raw5213step2 raw5213step2Labels := by
      have hz : ∀ j, raw5213step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5213step2 = (fun i j => raw5213step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5213step2 raw5213step1; decide +kernel
      have hl : raw5213step2Labels = raw5213step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213step1 raw5213step1Labels permutation20 hz
    mixedMoment B raw5213step2 raw5213step2Labels = mixedMoment B raw5213step3 raw5213step3Labels := by
      have hz : ∀ j, raw5213step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw5213step3 = (fun i j => raw5213step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw5213step3 raw5213step2; decide +kernel
      have hl : raw5213step3Labels = raw5213step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5213step2 raw5213step2Labels permutation4 hz
    mixedMoment B raw5213step3 raw5213step3Labels = mixedMoment B raw5213step4 raw5213step4Labels := by
      have hz : ∀ i, raw5213step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5213step4 = (fun i j => raw5213step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5213step4 raw5213step3; decide +kernel
      have hl : raw5213step4Labels = (fun j => raw5213step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5213step3 raw5213step3Labels permutation6 hz
    _ = mixedMoment B node4072 node4072Labels := by rfl

def raw5214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5214Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5214step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5214step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5214step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5214step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5214step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw5214step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5214step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw5214step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5214step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5214step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5214 raw5214Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5214 raw5214Labels = mixedMoment B raw5214step0 raw5214step0Labels := by
      have hz : ∀ j, raw5214 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5214step0 = (fun i j => raw5214 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5214step0 raw5214; decide +kernel
      have hl : raw5214step0Labels = raw5214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214 raw5214Labels permutation520 hz
    mixedMoment B raw5214step0 raw5214step0Labels = mixedMoment B raw5214step1 raw5214step1Labels := by
      have hz : ∀ j, raw5214step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5214step1 = (fun i j => raw5214step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5214step1 raw5214step0; decide +kernel
      have hl : raw5214step1Labels = raw5214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214step0 raw5214step0Labels permutation104 hz
    mixedMoment B raw5214step1 raw5214step1Labels = mixedMoment B raw5214step2 raw5214step2Labels := by
      have hz : ∀ j, raw5214step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5214step2 = (fun i j => raw5214step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5214step2 raw5214step1; decide +kernel
      have hl : raw5214step2Labels = raw5214step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5214step1 raw5214step1Labels permutation20 hz
    mixedMoment B raw5214step2 raw5214step2Labels = mixedMoment B raw5214step3 raw5214step3Labels := by
      have hz : ∀ i, raw5214step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5214step3 = (fun i j => raw5214step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5214step3 raw5214step2; decide +kernel
      have hl : raw5214step3Labels = (fun j => raw5214step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5214step2 raw5214step2Labels permutation6 hz
    mixedMoment B raw5214step3 raw5214step3Labels = mixedMoment B raw5214step4 raw5214step4Labels := by
      have ha : raw5214step4 = (fun i j => raw5214step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5214step4 raw5214step3; decide +kernel
      have hl : raw5214step4Labels = raw5214step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5214step3 raw5214step3Labels permutation7 permutation0
    mixedMoment B raw5214step4 raw5214step4Labels = mixedMoment B raw5214step5 raw5214step5Labels := by
      have ha : raw5214step5 = -raw5214step4 := by apply Matrix.ext; change ∀ i j, raw5214step5 i j = -(raw5214step4 i j); unfold raw5214step5 raw5214step4; decide +kernel
      have hl : raw5214step5Labels = raw5214step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw5215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5215Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5215step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5215step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5215step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5215step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5215step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw5215step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5215step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw5215step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5215step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5215step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5215 raw5215Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5215 raw5215Labels = mixedMoment B raw5215step0 raw5215step0Labels := by
      have hz : ∀ j, raw5215 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5215step0 = (fun i j => raw5215 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5215step0 raw5215; decide +kernel
      have hl : raw5215step0Labels = raw5215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5215 raw5215Labels permutation520 hz
    mixedMoment B raw5215step0 raw5215step0Labels = mixedMoment B raw5215step1 raw5215step1Labels := by
      have hz : ∀ j, raw5215step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5215step1 = (fun i j => raw5215step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5215step1 raw5215step0; decide +kernel
      have hl : raw5215step1Labels = raw5215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5215step0 raw5215step0Labels permutation104 hz
    mixedMoment B raw5215step1 raw5215step1Labels = mixedMoment B raw5215step2 raw5215step2Labels := by
      have hz : ∀ j, raw5215step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5215step2 = (fun i j => raw5215step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5215step2 raw5215step1; decide +kernel
      have hl : raw5215step2Labels = raw5215step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5215step1 raw5215step1Labels permutation14 hz
    mixedMoment B raw5215step2 raw5215step2Labels = mixedMoment B raw5215step3 raw5215step3Labels := by
      have hz : ∀ i, raw5215step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5215step3 = (fun i j => raw5215step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5215step3 raw5215step2; decide +kernel
      have hl : raw5215step3Labels = (fun j => raw5215step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5215step2 raw5215step2Labels permutation6 hz
    mixedMoment B raw5215step3 raw5215step3Labels = mixedMoment B raw5215step4 raw5215step4Labels := by
      have ha : raw5215step4 = (fun i j => raw5215step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5215step4 raw5215step3; decide +kernel
      have hl : raw5215step4Labels = raw5215step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5215step3 raw5215step3Labels permutation7 permutation0
    mixedMoment B raw5215step4 raw5215step4Labels = mixedMoment B raw5215step5 raw5215step5Labels := by
      have ha : raw5215step5 = -raw5215step4 := by apply Matrix.ext; change ∀ i j, raw5215step5 i j = -(raw5215step4 i j); unfold raw5215step5 raw5215step4; decide +kernel
      have hl : raw5215step5Labels = raw5215step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw5216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5216Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5216step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5216step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5216step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5216step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5216step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw5216step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5216step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw5216step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5216step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5216step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5216 raw5216Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5216 raw5216Labels = mixedMoment B raw5216step0 raw5216step0Labels := by
      have hz : ∀ j, raw5216 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5216step0 = (fun i j => raw5216 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5216step0 raw5216; decide +kernel
      have hl : raw5216step0Labels = raw5216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5216 raw5216Labels permutation520 hz
    mixedMoment B raw5216step0 raw5216step0Labels = mixedMoment B raw5216step1 raw5216step1Labels := by
      have hz : ∀ j, raw5216step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5216step1 = (fun i j => raw5216step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5216step1 raw5216step0; decide +kernel
      have hl : raw5216step1Labels = raw5216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5216step0 raw5216step0Labels permutation80 hz
    mixedMoment B raw5216step1 raw5216step1Labels = mixedMoment B raw5216step2 raw5216step2Labels := by
      have hz : ∀ j, raw5216step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5216step2 = (fun i j => raw5216step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5216step2 raw5216step1; decide +kernel
      have hl : raw5216step2Labels = raw5216step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5216step1 raw5216step1Labels permutation14 hz
    mixedMoment B raw5216step2 raw5216step2Labels = mixedMoment B raw5216step3 raw5216step3Labels := by
      have hz : ∀ i, raw5216step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5216step3 = (fun i j => raw5216step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5216step3 raw5216step2; decide +kernel
      have hl : raw5216step3Labels = (fun j => raw5216step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5216step2 raw5216step2Labels permutation6 hz
    mixedMoment B raw5216step3 raw5216step3Labels = mixedMoment B raw5216step4 raw5216step4Labels := by
      have ha : raw5216step4 = (fun i j => raw5216step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5216step4 raw5216step3; decide +kernel
      have hl : raw5216step4Labels = raw5216step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5216step3 raw5216step3Labels permutation7 permutation0
    mixedMoment B raw5216step4 raw5216step4Labels = mixedMoment B raw5216step5 raw5216step5Labels := by
      have ha : raw5216step5 = -raw5216step4 := by apply Matrix.ext; change ∀ i j, raw5216step5 i j = -(raw5216step4 i j); unfold raw5216step5 raw5216step4; decide +kernel
      have hl : raw5216step5Labels = raw5216step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw5217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5217step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5217step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5217step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5217step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5217step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw5217step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5217step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw5217step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5217step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5217step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5217 raw5217Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5217 raw5217Labels = mixedMoment B raw5217step0 raw5217step0Labels := by
      have hz : ∀ j, raw5217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5217step0 = (fun i j => raw5217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5217step0 raw5217; decide +kernel
      have hl : raw5217step0Labels = raw5217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5217 raw5217Labels permutation434 hz
    mixedMoment B raw5217step0 raw5217step0Labels = mixedMoment B raw5217step1 raw5217step1Labels := by
      have hz : ∀ j, raw5217step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5217step1 = (fun i j => raw5217step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5217step1 raw5217step0; decide +kernel
      have hl : raw5217step1Labels = raw5217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5217step0 raw5217step0Labels permutation80 hz
    mixedMoment B raw5217step1 raw5217step1Labels = mixedMoment B raw5217step2 raw5217step2Labels := by
      have hz : ∀ j, raw5217step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5217step2 = (fun i j => raw5217step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5217step2 raw5217step1; decide +kernel
      have hl : raw5217step2Labels = raw5217step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5217step1 raw5217step1Labels permutation14 hz
    mixedMoment B raw5217step2 raw5217step2Labels = mixedMoment B raw5217step3 raw5217step3Labels := by
      have hz : ∀ i, raw5217step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5217step3 = (fun i j => raw5217step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5217step3 raw5217step2; decide +kernel
      have hl : raw5217step3Labels = (fun j => raw5217step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5217step2 raw5217step2Labels permutation6 hz
    mixedMoment B raw5217step3 raw5217step3Labels = mixedMoment B raw5217step4 raw5217step4Labels := by
      have ha : raw5217step4 = (fun i j => raw5217step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5217step4 raw5217step3; decide +kernel
      have hl : raw5217step4Labels = raw5217step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5217step3 raw5217step3Labels permutation7 permutation0
    mixedMoment B raw5217step4 raw5217step4Labels = mixedMoment B raw5217step5 raw5217step5Labels := by
      have ha : raw5217step5 = -raw5217step4 := by apply Matrix.ext; change ∀ i j, raw5217step5 i j = -(raw5217step4 i j); unfold raw5217step5 raw5217step4; decide +kernel
      have hl : raw5217step5Labels = raw5217step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw5218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5218step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5218step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5218step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5218step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5218 raw5218Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw5218 raw5218Labels = mixedMoment B raw5218step0 raw5218step0Labels := by
      have ha : raw5218step0 = (fun i j => raw5218 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5218step0 raw5218; decide +kernel
      have hl : raw5218step0Labels = raw5218Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5218 raw5218Labels permutation168 permutation7
    mixedMoment B raw5218step0 raw5218step0Labels = mixedMoment B raw5218step1 raw5218step1Labels := by
      have ha : raw5218step1 = -raw5218step0 := by apply Matrix.ext; change ∀ i j, raw5218step1 i j = -(raw5218step0 i j); unfold raw5218step1 raw5218step0; decide +kernel
      have hl : raw5218step1Labels = raw5218step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5218step1 raw5218step1Labels = mixedMoment B raw5218step2 raw5218step2Labels := by
      have ha : raw5218step2 = raw5218step1 := by apply Matrix.ext; unfold raw5218step2 raw5218step1; decide +kernel
      have hl : raw5218step1Labels = labelEmbedding10 ∘ raw5218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5218step1 raw5218step1Labels raw5218step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw5219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw5219step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw5219step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5219step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw5219step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5219 raw5219Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw5219 raw5219Labels = mixedMoment B raw5219step0 raw5219step0Labels := by
      have hz : ∀ j, raw5219 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5219step0 = (fun i j => raw5219 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5219step0 raw5219; decide +kernel
      have hl : raw5219step0Labels = raw5219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5219 raw5219Labels permutation265 hz
    mixedMoment B raw5219step0 raw5219step0Labels = mixedMoment B raw5219step1 raw5219step1Labels := by
      have ha : raw5219step1 = (fun i j => raw5219step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5219step1 raw5219step0; decide +kernel
      have hl : raw5219step1Labels = raw5219step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5219step0 raw5219step0Labels permutation48 permutation7
    mixedMoment B raw5219step1 raw5219step1Labels = mixedMoment B raw5219step2 raw5219step2Labels := by
      have ha : raw5219step2 = -raw5219step1 := by apply Matrix.ext; change ∀ i j, raw5219step2 i j = -(raw5219step1 i j); unfold raw5219step2 raw5219step1; decide +kernel
      have hl : raw5219step2Labels = raw5219step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5219step2 raw5219step2Labels = mixedMoment B raw5219step3 raw5219step3Labels := by
      have ha : raw5219step3 = raw5219step2 := by apply Matrix.ext; unfold raw5219step3 raw5219step2; decide +kernel
      have hl : raw5219step2Labels = labelEmbedding10 ∘ raw5219step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5219step2 raw5219step2Labels raw5219step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw5220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw5220step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5220step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5220step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5220step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5220 raw5220Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw5220 raw5220Labels = mixedMoment B raw5220step0 raw5220step0Labels := by
      have hz : ∀ j, raw5220 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5220step0 = (fun i j => raw5220 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5220step0 raw5220; decide +kernel
      have hl : raw5220step0Labels = raw5220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5220 raw5220Labels permutation265 hz
    mixedMoment B raw5220step0 raw5220step0Labels = mixedMoment B raw5220step1 raw5220step1Labels := by
      have ha : raw5220step1 = (fun i j => raw5220step0 (permutation88 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5220step1 raw5220step0; decide +kernel
      have hl : raw5220step1Labels = raw5220step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5220step0 raw5220step0Labels permutation88 permutation4
    mixedMoment B raw5220step1 raw5220step1Labels = mixedMoment B raw5220step2 raw5220step2Labels := by
      have ha : raw5220step2 = -raw5220step1 := by apply Matrix.ext; change ∀ i j, raw5220step2 i j = -(raw5220step1 i j); unfold raw5220step2 raw5220step1; decide +kernel
      have hl : raw5220step2Labels = raw5220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5220step2 raw5220step2Labels = mixedMoment B raw5220step3 raw5220step3Labels := by
      have ha : raw5220step3 = raw5220step2 := by apply Matrix.ext; unfold raw5220step3 raw5220step2; decide +kernel
      have hl : raw5220step2Labels = labelEmbedding7 ∘ raw5220step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5220step2 raw5220step2Labels raw5220step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw5221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5221step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5221step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5221step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5221step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5221 raw5221Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw5221 raw5221Labels = mixedMoment B raw5221step0 raw5221step0Labels := by
      have hz : ∀ j, raw5221 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5221step0 = (fun i j => raw5221 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5221step0 raw5221; decide +kernel
      have hl : raw5221step0Labels = raw5221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5221 raw5221Labels permutation520 hz
    mixedMoment B raw5221step0 raw5221step0Labels = mixedMoment B raw5221step1 raw5221step1Labels := by
      have hz : ∀ j, raw5221step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5221step1 = (fun i j => raw5221step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5221step1 raw5221step0; decide +kernel
      have hl : raw5221step1Labels = raw5221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5221step0 raw5221step0Labels permutation56 hz
    mixedMoment B raw5221step1 raw5221step1Labels = mixedMoment B raw5221step2 raw5221step2Labels := by
      have ha : raw5221step2 = (fun i j => raw5221step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5221step2 raw5221step1; decide +kernel
      have hl : raw5221step2Labels = raw5221step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5221step1 raw5221step1Labels permutation12 permutation7
    mixedMoment B raw5221step2 raw5221step2Labels = mixedMoment B raw5221step3 raw5221step3Labels := by
      have ha : raw5221step3 = -raw5221step2 := by apply Matrix.ext; change ∀ i j, raw5221step3 i j = -(raw5221step2 i j); unfold raw5221step3 raw5221step2; decide +kernel
      have hl : raw5221step3Labels = raw5221step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5221step3 raw5221step3Labels = mixedMoment B raw5221step4 raw5221step4Labels := by
      have ha : raw5221step4 = raw5221step3 := by apply Matrix.ext; unfold raw5221step4 raw5221step3; decide +kernel
      have hl : raw5221step3Labels = labelEmbedding10 ∘ raw5221step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5221step3 raw5221step3Labels raw5221step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw5222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw5222step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5222step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5222step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5222 raw5222Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw5222 raw5222Labels = mixedMoment B raw5222step0 raw5222step0Labels := by
      have hz : ∀ j, raw5222 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5222step0 = (fun i j => raw5222 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5222step0 raw5222; decide +kernel
      have hl : raw5222step0Labels = raw5222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5222 raw5222Labels permutation265 hz
    mixedMoment B raw5222step0 raw5222step0Labels = mixedMoment B raw5222step1 raw5222step1Labels := by
      have ha : raw5222step1 = (fun i j => raw5222step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5222step1 raw5222step0; decide +kernel
      have hl : raw5222step1Labels = raw5222step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5222step0 raw5222step0Labels permutation48 permutation7
    mixedMoment B raw5222step1 raw5222step1Labels = mixedMoment B raw5222step2 raw5222step2Labels := by
      have ha : raw5222step2 = -raw5222step1 := by apply Matrix.ext; change ∀ i j, raw5222step2 i j = -(raw5222step1 i j); unfold raw5222step2 raw5222step1; decide +kernel
      have hl : raw5222step2Labels = raw5222step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5222step2 raw5222step2Labels = mixedMoment B raw5222step3 raw5222step3Labels := by
      have ha : raw5222step3 = raw5222step2 := by apply Matrix.ext; unfold raw5222step3 raw5222step2; decide +kernel
      have hl : raw5222step2Labels = labelEmbedding10 ∘ raw5222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5222step2 raw5222step2Labels raw5222step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw5223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5223 raw5223Labels = mixedMoment B node4446 node4446Labels := by
  calc
    mixedMoment B raw5223 raw5223Labels = mixedMoment B raw5223step0 raw5223step0Labels := by
      have ha : raw5223step0 = (fun i j => raw5223 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5223step0 raw5223; decide +kernel
      have hl : raw5223step0Labels = raw5223Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5223 raw5223Labels permutation182 permutation2
    _ = mixedMoment B node4446 node4446Labels := by rfl

def raw5224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5224 raw5224Labels = mixedMoment B node4857 node4857Labels := by
  calc
    mixedMoment B raw5224 raw5224Labels = mixedMoment B raw5224step0 raw5224step0Labels := by
      have ha : raw5224step0 = (fun i j => raw5224 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5224step0 raw5224; decide +kernel
      have hl : raw5224step0Labels = raw5224Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5224 raw5224Labels permutation182 permutation2
    _ = mixedMoment B node4857 node4857Labels := by rfl

def raw5225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5225 raw5225Labels = mixedMoment B node4876 node4876Labels := by
  calc
    mixedMoment B raw5225 raw5225Labels = mixedMoment B raw5225step0 raw5225step0Labels := by
      have ha : raw5225step0 = (fun i j => raw5225 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5225step0 raw5225; decide +kernel
      have hl : raw5225step0Labels = raw5225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5225 raw5225Labels permutation206 permutation2
    _ = mixedMoment B node4876 node4876Labels := by rfl

def raw5226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5226 raw5226Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw5226 raw5226Labels = mixedMoment B raw5226step0 raw5226step0Labels := by
      have hz : ∀ j, raw5226 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5226step0 = (fun i j => raw5226 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5226step0 raw5226; decide +kernel
      have hl : raw5226step0Labels = raw5226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5226 raw5226Labels permutation520 hz
    mixedMoment B raw5226step0 raw5226step0Labels = mixedMoment B raw5226step1 raw5226step1Labels := by
      have ha : raw5226step1 = (fun i j => raw5226step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5226step1 raw5226step0; decide +kernel
      have hl : raw5226step1Labels = raw5226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5226step0 raw5226step0Labels permutation40 permutation2
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw5227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw5227step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5227step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5227step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5227 raw5227Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw5227 raw5227Labels = mixedMoment B raw5227step0 raw5227step0Labels := by
      have ha : raw5227step0 = (fun i j => raw5227 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5227step0 raw5227; decide +kernel
      have hl : raw5227step0Labels = raw5227Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5227 raw5227Labels permutation168 permutation7
    mixedMoment B raw5227step0 raw5227step0Labels = mixedMoment B raw5227step1 raw5227step1Labels := by
      have ha : raw5227step1 = -raw5227step0 := by apply Matrix.ext; change ∀ i j, raw5227step1 i j = -(raw5227step0 i j); unfold raw5227step1 raw5227step0; decide +kernel
      have hl : raw5227step1Labels = raw5227step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5227step1 raw5227step1Labels = mixedMoment B raw5227step2 raw5227step2Labels := by
      have ha : raw5227step2 = raw5227step1 := by apply Matrix.ext; unfold raw5227step2 raw5227step1; decide +kernel
      have hl : raw5227step1Labels = labelEmbedding10 ∘ raw5227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5227step1 raw5227step1Labels raw5227step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw5228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5228 raw5228Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw5228 raw5228Labels = mixedMoment B raw5228step0 raw5228step0Labels := by
      have hz : ∀ j, raw5228 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5228step0 = (fun i j => raw5228 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5228step0 raw5228; decide +kernel
      have hl : raw5228step0Labels = raw5228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5228 raw5228Labels permutation265 hz
    mixedMoment B raw5228step0 raw5228step0Labels = mixedMoment B raw5228step1 raw5228step1Labels := by
      have ha : raw5228step1 = (fun i j => raw5228step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5228step1 raw5228step0; decide +kernel
      have hl : raw5228step1Labels = raw5228step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5228step0 raw5228step0Labels permutation40 permutation2
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw5229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5229 raw5229Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw5229 raw5229Labels = mixedMoment B raw5229step0 raw5229step0Labels := by
      have ha : raw5229step0 = (fun i j => raw5229 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5229step0 raw5229; decide +kernel
      have hl : raw5229step0Labels = raw5229Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5229 raw5229Labels permutation160 permutation2
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw5230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5230 raw5230Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw5230 raw5230Labels = mixedMoment B raw5230step0 raw5230step0Labels := by
      have hz : ∀ j, raw5230 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5230step0 = (fun i j => raw5230 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5230step0 raw5230; decide +kernel
      have hl : raw5230step0Labels = raw5230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5230 raw5230Labels permutation265 hz
    mixedMoment B raw5230step0 raw5230step0Labels = mixedMoment B raw5230step1 raw5230step1Labels := by
      have ha : raw5230step1 = (fun i j => raw5230step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5230step1 raw5230step0; decide +kernel
      have hl : raw5230step1Labels = raw5230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5230step0 raw5230step0Labels permutation40 permutation2
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw5231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5231step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5231step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5231 raw5231Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw5231 raw5231Labels = mixedMoment B raw5231step0 raw5231step0Labels := by
      have hz : ∀ j, raw5231 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5231step0 = (fun i j => raw5231 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5231step0 raw5231; decide +kernel
      have hl : raw5231step0Labels = raw5231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5231 raw5231Labels permutation520 hz
    mixedMoment B raw5231step0 raw5231step0Labels = mixedMoment B raw5231step1 raw5231step1Labels := by
      have hz : ∀ j, raw5231step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5231step1 = (fun i j => raw5231step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5231step1 raw5231step0; decide +kernel
      have hl : raw5231step1Labels = raw5231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5231step0 raw5231step0Labels permutation56 hz
    mixedMoment B raw5231step1 raw5231step1Labels = mixedMoment B raw5231step2 raw5231step2Labels := by
      have ha : raw5231step2 = (fun i j => raw5231step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5231step2 raw5231step1; decide +kernel
      have hl : raw5231step2Labels = raw5231step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5231step1 raw5231step1Labels permutation10 permutation2
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw5232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5232step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5232step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5232step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5232step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5232 raw5232Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw5232 raw5232Labels = mixedMoment B raw5232step0 raw5232step0Labels := by
      have hz : ∀ j, raw5232 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5232step0 = (fun i j => raw5232 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5232step0 raw5232; decide +kernel
      have hl : raw5232step0Labels = raw5232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5232 raw5232Labels permutation265 hz
    mixedMoment B raw5232step0 raw5232step0Labels = mixedMoment B raw5232step1 raw5232step1Labels := by
      have ha : raw5232step1 = (fun i j => raw5232step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5232step1 raw5232step0; decide +kernel
      have hl : raw5232step1Labels = raw5232step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5232step0 raw5232step0Labels permutation48 permutation7
    mixedMoment B raw5232step1 raw5232step1Labels = mixedMoment B raw5232step2 raw5232step2Labels := by
      have ha : raw5232step2 = -raw5232step1 := by apply Matrix.ext; change ∀ i j, raw5232step2 i j = -(raw5232step1 i j); unfold raw5232step2 raw5232step1; decide +kernel
      have hl : raw5232step2Labels = raw5232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5232step2 raw5232step2Labels = mixedMoment B raw5232step3 raw5232step3Labels := by
      have ha : raw5232step3 = raw5232step2 := by apply Matrix.ext; unfold raw5232step3 raw5232step2; decide +kernel
      have hl : raw5232step2Labels = labelEmbedding10 ∘ raw5232step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5232step2 raw5232step2Labels raw5232step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw5233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5233 raw5233Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw5233 raw5233Labels = mixedMoment B raw5233step0 raw5233step0Labels := by
      have hz : ∀ j, raw5233 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5233step0 = (fun i j => raw5233 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5233step0 raw5233; decide +kernel
      have hl : raw5233step0Labels = raw5233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5233 raw5233Labels permutation265 hz
    mixedMoment B raw5233step0 raw5233step0Labels = mixedMoment B raw5233step1 raw5233step1Labels := by
      have ha : raw5233step1 = (fun i j => raw5233step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5233step1 raw5233step0; decide +kernel
      have hl : raw5233step1Labels = raw5233step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5233step0 raw5233step0Labels permutation34 permutation2
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw5234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5234 raw5234Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw5234 raw5234Labels = mixedMoment B raw5234step0 raw5234step0Labels := by
      have ha : raw5234step0 = (fun i j => raw5234 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5234step0 raw5234; decide +kernel
      have hl : raw5234step0Labels = raw5234Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5234 raw5234Labels permutation154 permutation2
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw5235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5235 raw5235Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw5235 raw5235Labels = mixedMoment B raw5235step0 raw5235step0Labels := by
      have hz : ∀ j, raw5235 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5235step0 = (fun i j => raw5235 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5235step0 raw5235; decide +kernel
      have hl : raw5235step0Labels = raw5235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5235 raw5235Labels permutation265 hz
    mixedMoment B raw5235step0 raw5235step0Labels = mixedMoment B raw5235step1 raw5235step1Labels := by
      have ha : raw5235step1 = (fun i j => raw5235step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5235step1 raw5235step0; decide +kernel
      have hl : raw5235step1Labels = raw5235step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5235step0 raw5235step0Labels permutation34 permutation2
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw5236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5236 raw5236Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw5236 raw5236Labels = mixedMoment B raw5236step0 raw5236step0Labels := by
      have hz : ∀ j, raw5236 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5236step0 = (fun i j => raw5236 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5236step0 raw5236; decide +kernel
      have hl : raw5236step0Labels = raw5236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5236 raw5236Labels permutation520 hz
    mixedMoment B raw5236step0 raw5236step0Labels = mixedMoment B raw5236step1 raw5236step1Labels := by
      have hz : ∀ j, raw5236step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5236step1 = (fun i j => raw5236step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5236step1 raw5236step0; decide +kernel
      have hl : raw5236step1Labels = raw5236step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5236step0 raw5236step0Labels permutation56 hz
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw5237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw5237step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5237step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5237step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5237step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5237 raw5237Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw5237 raw5237Labels = mixedMoment B raw5237step0 raw5237step0Labels := by
      have hz : ∀ j, raw5237 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5237step0 = (fun i j => raw5237 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5237step0 raw5237; decide +kernel
      have hl : raw5237step0Labels = raw5237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5237 raw5237Labels permutation265 hz
    mixedMoment B raw5237step0 raw5237step0Labels = mixedMoment B raw5237step1 raw5237step1Labels := by
      have ha : raw5237step1 = (fun i j => raw5237step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5237step1 raw5237step0; decide +kernel
      have hl : raw5237step1Labels = raw5237step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5237step0 raw5237step0Labels permutation48 permutation7
    mixedMoment B raw5237step1 raw5237step1Labels = mixedMoment B raw5237step2 raw5237step2Labels := by
      have ha : raw5237step2 = -raw5237step1 := by apply Matrix.ext; change ∀ i j, raw5237step2 i j = -(raw5237step1 i j); unfold raw5237step2 raw5237step1; decide +kernel
      have hl : raw5237step2Labels = raw5237step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5237step2 raw5237step2Labels = mixedMoment B raw5237step3 raw5237step3Labels := by
      have ha : raw5237step3 = raw5237step2 := by apply Matrix.ext; unfold raw5237step3 raw5237step2; decide +kernel
      have hl : raw5237step2Labels = labelEmbedding10 ∘ raw5237step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5237step2 raw5237step2Labels raw5237step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw5238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5238 raw5238Labels = mixedMoment B node4448 node4448Labels := by
  calc
    mixedMoment B raw5238 raw5238Labels = mixedMoment B raw5238step0 raw5238step0Labels := by
      have hz : ∀ j, raw5238 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5238step0 = (fun i j => raw5238 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5238step0 raw5238; decide +kernel
      have hl : raw5238step0Labels = raw5238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5238 raw5238Labels permutation265 hz
    _ = mixedMoment B node4448 node4448Labels := by rfl

def raw5239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5239 raw5239Labels = mixedMoment B node4796 node4796Labels := by
  calc
    _ = mixedMoment B node4796 node4796Labels := by rfl

def raw5240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5240 raw5240Labels = mixedMoment B node4858 node4858Labels := by
  calc
    mixedMoment B raw5240 raw5240Labels = mixedMoment B raw5240step0 raw5240step0Labels := by
      have hz : ∀ j, raw5240 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5240step0 = (fun i j => raw5240 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5240step0 raw5240; decide +kernel
      have hl : raw5240step0Labels = raw5240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5240 raw5240Labels permutation265 hz
    _ = mixedMoment B node4858 node4858Labels := by rfl

def raw5241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5241 raw5241Labels = mixedMoment B node4877 node4877Labels := by
  calc
    mixedMoment B raw5241 raw5241Labels = mixedMoment B raw5241step0 raw5241step0Labels := by
      have hz : ∀ j, raw5241 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5241step0 = (fun i j => raw5241 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5241step0 raw5241; decide +kernel
      have hl : raw5241step0Labels = raw5241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5241 raw5241Labels permutation265 hz
    mixedMoment B raw5241step0 raw5241step0Labels = mixedMoment B raw5241step1 raw5241step1Labels := by
      have ha : raw5241step1 = (fun i j => raw5241step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5241step1 raw5241step0; decide +kernel
      have hl : raw5241step1Labels = raw5241step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5241step0 raw5241step0Labels permutation38 permutation2
    _ = mixedMoment B node4877 node4877Labels := by rfl

def raw5242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5242 raw5242Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw5242 raw5242Labels = mixedMoment B raw5242step0 raw5242step0Labels := by
      have hz : ∀ j, raw5242 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5242step0 = (fun i j => raw5242 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5242step0 raw5242; decide +kernel
      have hl : raw5242step0Labels = raw5242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5242 raw5242Labels permutation265 hz
    mixedMoment B raw5242step0 raw5242step0Labels = mixedMoment B raw5242step1 raw5242step1Labels := by
      have ha : raw5242step1 = (fun i j => raw5242step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5242step1 raw5242step0; decide +kernel
      have hl : raw5242step1Labels = raw5242step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5242step0 raw5242step0Labels permutation33 permutation2
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw5243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5243 raw5243Labels = mixedMoment B node4447 node4447Labels := by
  calc
    mixedMoment B raw5243 raw5243Labels = mixedMoment B raw5243step0 raw5243step0Labels := by
      have hz : ∀ j, raw5243 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5243step0 = (fun i j => raw5243 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5243step0 raw5243; decide +kernel
      have hl : raw5243step0Labels = raw5243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5243 raw5243Labels permutation265 hz
    _ = mixedMoment B node4447 node4447Labels := by rfl

def raw5244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw5244step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw5244step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5244step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw5244step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5244 raw5244Labels = mixedMoment B node4734 node4734Labels := by
  calc
    mixedMoment B raw5244 raw5244Labels = mixedMoment B raw5244step0 raw5244step0Labels := by
      have ha : raw5244step0 = (fun i j => raw5244 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5244step0 raw5244; decide +kernel
      have hl : raw5244step0Labels = raw5244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5244 raw5244Labels permutation682 permutation3
    mixedMoment B raw5244step0 raw5244step0Labels = mixedMoment B raw5244step1 raw5244step1Labels := by
      have ha : raw5244step1 = -raw5244step0 := by apply Matrix.ext; change ∀ i j, raw5244step1 i j = -(raw5244step0 i j); unfold raw5244step1 raw5244step0; decide +kernel
      have hl : raw5244step1Labels = raw5244step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5244step1 raw5244step1Labels = mixedMoment B raw5244step2 raw5244step2Labels := by
      have ha : raw5244step2 = raw5244step1 := by apply Matrix.ext; unfold raw5244step2 raw5244step1; decide +kernel
      have hl : raw5244step1Labels = labelEmbedding6 ∘ raw5244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5244step1 raw5244step1Labels raw5244step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4734 node4734Labels := by rfl

def raw5245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw5245step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw5245step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5245step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw5245step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5245 raw5245Labels = mixedMoment B node4748 node4748Labels := by
  calc
    mixedMoment B raw5245 raw5245Labels = mixedMoment B raw5245step0 raw5245step0Labels := by
      have hz : ∀ j, raw5245 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5245step0 = (fun i j => raw5245 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5245step0 raw5245; decide +kernel
      have hl : raw5245step0Labels = raw5245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5245 raw5245Labels permutation265 hz
    mixedMoment B raw5245step0 raw5245step0Labels = mixedMoment B raw5245step1 raw5245step1Labels := by
      have ha : raw5245step1 = (fun i j => raw5245step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5245step1 raw5245step0; decide +kernel
      have hl : raw5245step1Labels = raw5245step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5245step0 raw5245step0Labels permutation151 permutation3
    mixedMoment B raw5245step1 raw5245step1Labels = mixedMoment B raw5245step2 raw5245step2Labels := by
      have ha : raw5245step2 = -raw5245step1 := by apply Matrix.ext; change ∀ i j, raw5245step2 i j = -(raw5245step1 i j); unfold raw5245step2 raw5245step1; decide +kernel
      have hl : raw5245step2Labels = raw5245step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5245step2 raw5245step2Labels = mixedMoment B raw5245step3 raw5245step3Labels := by
      have ha : raw5245step3 = raw5245step2 := by apply Matrix.ext; unfold raw5245step3 raw5245step2; decide +kernel
      have hl : raw5245step2Labels = labelEmbedding6 ∘ raw5245step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5245step2 raw5245step2Labels raw5245step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4748 node4748Labels := by rfl

def raw5246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw5246step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw5246step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5246step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw5246step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5246 raw5246Labels = mixedMoment B node4743 node4743Labels := by
  calc
    mixedMoment B raw5246 raw5246Labels = mixedMoment B raw5246step0 raw5246step0Labels := by
      have hz : ∀ j, raw5246 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5246step0 = (fun i j => raw5246 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5246step0 raw5246; decide +kernel
      have hl : raw5246step0Labels = raw5246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5246 raw5246Labels permutation265 hz
    mixedMoment B raw5246step0 raw5246step0Labels = mixedMoment B raw5246step1 raw5246step1Labels := by
      have ha : raw5246step1 = (fun i j => raw5246step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5246step1 raw5246step0; decide +kernel
      have hl : raw5246step1Labels = raw5246step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5246step0 raw5246step0Labels permutation149 permutation3
    mixedMoment B raw5246step1 raw5246step1Labels = mixedMoment B raw5246step2 raw5246step2Labels := by
      have ha : raw5246step2 = -raw5246step1 := by apply Matrix.ext; change ∀ i j, raw5246step2 i j = -(raw5246step1 i j); unfold raw5246step2 raw5246step1; decide +kernel
      have hl : raw5246step2Labels = raw5246step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5246step2 raw5246step2Labels = mixedMoment B raw5246step3 raw5246step3Labels := by
      have ha : raw5246step3 = raw5246step2 := by apply Matrix.ext; unfold raw5246step3 raw5246step2; decide +kernel
      have hl : raw5246step2Labels = labelEmbedding6 ∘ raw5246step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5246step2 raw5246step2Labels raw5246step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4743 node4743Labels := by rfl

def raw5247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw5247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5247 raw5247Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw5247 raw5247Labels = mixedMoment B raw5247step0 raw5247step0Labels := by
      have hz : ∀ j, raw5247 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5247step0 = (fun i j => raw5247 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5247step0 raw5247; decide +kernel
      have hl : raw5247step0Labels = raw5247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5247 raw5247Labels permutation520 hz
    mixedMoment B raw5247step0 raw5247step0Labels = mixedMoment B raw5247step1 raw5247step1Labels := by
      have hz : ∀ j, raw5247step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5247step1 = (fun i j => raw5247step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5247step1 raw5247step0; decide +kernel
      have hl : raw5247step1Labels = raw5247step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5247step0 raw5247step0Labels permutation56 hz
    _ = mixedMoment B node4892 node4892Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
