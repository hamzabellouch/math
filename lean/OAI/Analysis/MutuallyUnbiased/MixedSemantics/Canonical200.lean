import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
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

def raw25600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw25600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw25600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25600 raw25600Labels = mixedMoment B node1071 node1071Labels := by
  calc
    mixedMoment B raw25600 raw25600Labels = mixedMoment B raw25600step0 raw25600step0Labels := by
      have hz : ∀ j, raw25600 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25600step0 = (fun i j => raw25600 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25600step0 raw25600; decide +kernel
      have hl : raw25600step0Labels = raw25600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25600 raw25600Labels permutation265 hz
    mixedMoment B raw25600step0 raw25600step0Labels = mixedMoment B raw25600step1 raw25600step1Labels := by
      have ha : raw25600step1 = (fun i j => raw25600step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25600step1 raw25600step0; decide +kernel
      have hl : raw25600step1Labels = raw25600step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25600step0 raw25600step0Labels permutation50 permutation2
    _ = mixedMoment B node1071 node1071Labels := by rfl

def raw25601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2], ![1, -2, 1]]
def raw25601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 1, -2], ![1, -2, 1]]
def raw25601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 1, -2], ![1, -2, 1]]
def raw25601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25601 raw25601Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw25601 raw25601Labels = mixedMoment B raw25601step0 raw25601step0Labels := by
      have hz : ∀ j, raw25601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25601step0 = (fun i j => raw25601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25601step0 raw25601; decide +kernel
      have hl : raw25601step0Labels = raw25601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25601 raw25601Labels permutation346 hz
    mixedMoment B raw25601step0 raw25601step0Labels = mixedMoment B raw25601step1 raw25601step1Labels := by
      have hz : ∀ j, raw25601step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25601step1 = (fun i j => raw25601step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25601step1 raw25601step0; decide +kernel
      have hl : raw25601step1Labels = raw25601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25601step0 raw25601step0Labels permutation56 hz
    mixedMoment B raw25601step1 raw25601step1Labels = mixedMoment B raw25601step2 raw25601step2Labels := by
      have ha : raw25601step2 = (fun i j => raw25601step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25601step2 raw25601step1; decide +kernel
      have hl : raw25601step2Labels = raw25601step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25601step1 raw25601step1Labels permutation13 permutation2
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw25602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2], ![1, -2, 1]]
def raw25602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2], ![1, -2, 1]]
def raw25602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, 0, -2], ![1, -2, 1]]
def raw25602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25602 raw25602Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw25602 raw25602Labels = mixedMoment B raw25602step0 raw25602step0Labels := by
      have hz : ∀ j, raw25602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25602step0 = (fun i j => raw25602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25602step0 raw25602; decide +kernel
      have hl : raw25602step0Labels = raw25602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25602 raw25602Labels permutation346 hz
    mixedMoment B raw25602step0 raw25602step0Labels = mixedMoment B raw25602step1 raw25602step1Labels := by
      have hz : ∀ j, raw25602step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25602step1 = (fun i j => raw25602step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25602step1 raw25602step0; decide +kernel
      have hl : raw25602step1Labels = raw25602step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25602step0 raw25602step0Labels permutation56 hz
    mixedMoment B raw25602step1 raw25602step1Labels = mixedMoment B raw25602step2 raw25602step2Labels := by
      have ha : raw25602step2 = (fun i j => raw25602step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25602step2 raw25602step1; decide +kernel
      have hl : raw25602step2Labels = raw25602step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25602step1 raw25602step1Labels permutation12 permutation2
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw25603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25603 raw25603Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw25603 raw25603Labels = mixedMoment B raw25603step0 raw25603step0Labels := by
      have hz : ∀ j, raw25603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25603step0 = (fun i j => raw25603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25603step0 raw25603; decide +kernel
      have hl : raw25603step0Labels = raw25603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25603 raw25603Labels permutation346 hz
    mixedMoment B raw25603step0 raw25603step0Labels = mixedMoment B raw25603step1 raw25603step1Labels := by
      have ha : raw25603step1 = (fun i j => raw25603step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25603step1 raw25603step0; decide +kernel
      have hl : raw25603step1Labels = raw25603step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25603step0 raw25603step0Labels permutation34 permutation2
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw25604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25604 raw25604Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw25604 raw25604Labels = mixedMoment B raw25604step0 raw25604step0Labels := by
      have hz : ∀ j, raw25604 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25604step0 = (fun i j => raw25604 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25604step0 raw25604; decide +kernel
      have hl : raw25604step0Labels = raw25604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25604 raw25604Labels permutation265 hz
    mixedMoment B raw25604step0 raw25604step0Labels = mixedMoment B raw25604step1 raw25604step1Labels := by
      have ha : raw25604step1 = (fun i j => raw25604step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25604step1 raw25604step0; decide +kernel
      have hl : raw25604step1Labels = raw25604step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25604step0 raw25604step0Labels permutation34 permutation2
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw25605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25605 raw25605Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw25605 raw25605Labels = mixedMoment B raw25605step0 raw25605step0Labels := by
      have hz : ∀ j, raw25605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25605step0 = (fun i j => raw25605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25605step0 raw25605; decide +kernel
      have hl : raw25605step0Labels = raw25605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25605 raw25605Labels permutation346 hz
    mixedMoment B raw25605step0 raw25605step0Labels = mixedMoment B raw25605step1 raw25605step1Labels := by
      have hz : ∀ j, raw25605step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25605step1 = (fun i j => raw25605step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25605step1 raw25605step0; decide +kernel
      have hl : raw25605step1Labels = raw25605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25605step0 raw25605step0Labels permutation56 hz
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw25606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25606 raw25606Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw25606 raw25606Labels = mixedMoment B raw25606step0 raw25606step0Labels := by
      have hz : ∀ j, raw25606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25606step0 = (fun i j => raw25606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25606step0 raw25606; decide +kernel
      have hl : raw25606step0Labels = raw25606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25606 raw25606Labels permutation346 hz
    mixedMoment B raw25606step0 raw25606step0Labels = mixedMoment B raw25606step1 raw25606step1Labels := by
      have hz : ∀ j, raw25606step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25606step1 = (fun i j => raw25606step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25606step1 raw25606step0; decide +kernel
      have hl : raw25606step1Labels = raw25606step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25606step0 raw25606step0Labels permutation56 hz
    mixedMoment B raw25606step1 raw25606step1Labels = mixedMoment B raw25606step2 raw25606step2Labels := by
      have ha : raw25606step2 = (fun i j => raw25606step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25606step2 raw25606step1; decide +kernel
      have hl : raw25606step2Labels = raw25606step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25606step1 raw25606step1Labels permutation10 permutation2
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw25607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25607step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25607step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25607step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25607step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25607 raw25607Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw25607 raw25607Labels = mixedMoment B raw25607step0 raw25607step0Labels := by
      have hz : ∀ j, raw25607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25607step0 = (fun i j => raw25607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25607step0 raw25607; decide +kernel
      have hl : raw25607step0Labels = raw25607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25607 raw25607Labels permutation346 hz
    mixedMoment B raw25607step0 raw25607step0Labels = mixedMoment B raw25607step1 raw25607step1Labels := by
      have hz : ∀ j, raw25607step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25607step1 = (fun i j => raw25607step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25607step1 raw25607step0; decide +kernel
      have hl : raw25607step1Labels = raw25607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25607step0 raw25607step0Labels permutation56 hz
    mixedMoment B raw25607step1 raw25607step1Labels = mixedMoment B raw25607step2 raw25607step2Labels := by
      have ha : raw25607step2 = (fun i j => raw25607step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25607step2 raw25607step1; decide +kernel
      have hl : raw25607step2Labels = raw25607step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25607step1 raw25607step1Labels permutation13 permutation7
    mixedMoment B raw25607step2 raw25607step2Labels = mixedMoment B raw25607step3 raw25607step3Labels := by
      have ha : raw25607step3 = -raw25607step2 := by apply Matrix.ext; change ∀ i j, raw25607step3 i j = -(raw25607step2 i j); unfold raw25607step3 raw25607step2; decide +kernel
      have hl : raw25607step3Labels = raw25607step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25607step3 raw25607step3Labels = mixedMoment B raw25607step4 raw25607step4Labels := by
      have ha : raw25607step4 = raw25607step3 := by apply Matrix.ext; unfold raw25607step4 raw25607step3; decide +kernel
      have hl : raw25607step3Labels = labelEmbedding10 ∘ raw25607step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25607step3 raw25607step3Labels raw25607step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw25608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25608 raw25608Labels = mixedMoment B node4176 node4176Labels := by
  calc
    mixedMoment B raw25608 raw25608Labels = mixedMoment B raw25608step0 raw25608step0Labels := by
      have hz : ∀ j, raw25608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25608step0 = (fun i j => raw25608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25608step0 raw25608; decide +kernel
      have hl : raw25608step0Labels = raw25608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25608 raw25608Labels permutation346 hz
    mixedMoment B raw25608step0 raw25608step0Labels = mixedMoment B raw25608step1 raw25608step1Labels := by
      have ha : raw25608step1 = (fun i j => raw25608step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25608step1 raw25608step0; decide +kernel
      have hl : raw25608step1Labels = raw25608step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25608step0 raw25608step0Labels permutation34 permutation2
    _ = mixedMoment B node4176 node4176Labels := by rfl

def raw25609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25609 raw25609Labels = mixedMoment B node4345 node4345Labels := by
  calc
    mixedMoment B raw25609 raw25609Labels = mixedMoment B raw25609step0 raw25609step0Labels := by
      have ha : raw25609step0 = (fun i j => raw25609 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25609step0 raw25609; decide +kernel
      have hl : raw25609step0Labels = raw25609Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25609 raw25609Labels permutation178 permutation2
    _ = mixedMoment B node4345 node4345Labels := by rfl

def raw25610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25610 raw25610Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw25610 raw25610Labels = mixedMoment B raw25610step0 raw25610step0Labels := by
      have hz : ∀ j, raw25610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25610step0 = (fun i j => raw25610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25610step0 raw25610; decide +kernel
      have hl : raw25610step0Labels = raw25610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25610 raw25610Labels permutation346 hz
    mixedMoment B raw25610step0 raw25610step0Labels = mixedMoment B raw25610step1 raw25610step1Labels := by
      have ha : raw25610step1 = (fun i j => raw25610step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25610step1 raw25610step0; decide +kernel
      have hl : raw25610step1Labels = raw25610step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25610step0 raw25610step0Labels permutation38 permutation2
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw25611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25611 raw25611Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw25611 raw25611Labels = mixedMoment B raw25611step0 raw25611step0Labels := by
      have hz : ∀ j, raw25611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25611step0 = (fun i j => raw25611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25611step0 raw25611; decide +kernel
      have hl : raw25611step0Labels = raw25611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25611 raw25611Labels permutation346 hz
    mixedMoment B raw25611step0 raw25611step0Labels = mixedMoment B raw25611step1 raw25611step1Labels := by
      have ha : raw25611step1 = (fun i j => raw25611step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25611step1 raw25611step0; decide +kernel
      have hl : raw25611step1Labels = raw25611step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25611step0 raw25611step0Labels permutation44 permutation2
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw25612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25612step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25612 raw25612Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25612 raw25612Labels = mixedMoment B raw25612step0 raw25612step0Labels := by
      have hz : ∀ j, raw25612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25612step0 = (fun i j => raw25612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25612step0 raw25612; decide +kernel
      have hl : raw25612step0Labels = raw25612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25612 raw25612Labels permutation346 hz
    mixedMoment B raw25612step0 raw25612step0Labels = mixedMoment B raw25612step1 raw25612step1Labels := by
      have ha : raw25612step1 = (fun i j => raw25612step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25612step1 raw25612step0; decide +kernel
      have hl : raw25612step1Labels = raw25612step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25612step0 raw25612step0Labels permutation37 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw25613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25613 raw25613Labels = mixedMoment B node4176 node4176Labels := by
  calc
    mixedMoment B raw25613 raw25613Labels = mixedMoment B raw25613step0 raw25613step0Labels := by
      have hz : ∀ j, raw25613 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25613step0 = (fun i j => raw25613 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25613step0 raw25613; decide +kernel
      have hl : raw25613step0Labels = raw25613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25613 raw25613Labels permutation265 hz
    mixedMoment B raw25613step0 raw25613step0Labels = mixedMoment B raw25613step1 raw25613step1Labels := by
      have ha : raw25613step1 = (fun i j => raw25613step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25613step1 raw25613step0; decide +kernel
      have hl : raw25613step1Labels = raw25613step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25613step0 raw25613step0Labels permutation34 permutation2
    _ = mixedMoment B node4176 node4176Labels := by rfl

def raw25614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25614 raw25614Labels = mixedMoment B node4345 node4345Labels := by
  calc
    mixedMoment B raw25614 raw25614Labels = mixedMoment B raw25614step0 raw25614step0Labels := by
      have ha : raw25614step0 = (fun i j => raw25614 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25614step0 raw25614; decide +kernel
      have hl : raw25614step0Labels = raw25614Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25614 raw25614Labels permutation154 permutation2
    _ = mixedMoment B node4345 node4345Labels := by rfl

def raw25615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25615 raw25615Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw25615 raw25615Labels = mixedMoment B raw25615step0 raw25615step0Labels := by
      have hz : ∀ j, raw25615 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25615step0 = (fun i j => raw25615 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25615step0 raw25615; decide +kernel
      have hl : raw25615step0Labels = raw25615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25615 raw25615Labels permutation265 hz
    mixedMoment B raw25615step0 raw25615step0Labels = mixedMoment B raw25615step1 raw25615step1Labels := by
      have ha : raw25615step1 = (fun i j => raw25615step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25615step1 raw25615step0; decide +kernel
      have hl : raw25615step1Labels = raw25615step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25615step0 raw25615step0Labels permutation38 permutation2
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw25616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25616 raw25616Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw25616 raw25616Labels = mixedMoment B raw25616step0 raw25616step0Labels := by
      have hz : ∀ j, raw25616 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25616step0 = (fun i j => raw25616 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25616step0 raw25616; decide +kernel
      have hl : raw25616step0Labels = raw25616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25616 raw25616Labels permutation265 hz
    mixedMoment B raw25616step0 raw25616step0Labels = mixedMoment B raw25616step1 raw25616step1Labels := by
      have ha : raw25616step1 = (fun i j => raw25616step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25616step1 raw25616step0; decide +kernel
      have hl : raw25616step1Labels = raw25616step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25616step0 raw25616step0Labels permutation44 permutation2
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw25617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25617 raw25617Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25617 raw25617Labels = mixedMoment B raw25617step0 raw25617step0Labels := by
      have hz : ∀ j, raw25617 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25617step0 = (fun i j => raw25617 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25617step0 raw25617; decide +kernel
      have hl : raw25617step0Labels = raw25617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25617 raw25617Labels permutation265 hz
    mixedMoment B raw25617step0 raw25617step0Labels = mixedMoment B raw25617step1 raw25617step1Labels := by
      have ha : raw25617step1 = (fun i j => raw25617step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25617step1 raw25617step0; decide +kernel
      have hl : raw25617step1Labels = raw25617step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25617step0 raw25617step0Labels permutation37 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw25618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25618 raw25618Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw25618 raw25618Labels = mixedMoment B raw25618step0 raw25618step0Labels := by
      have hz : ∀ j, raw25618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25618step0 = (fun i j => raw25618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25618step0 raw25618; decide +kernel
      have hl : raw25618step0Labels = raw25618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25618 raw25618Labels permutation346 hz
    mixedMoment B raw25618step0 raw25618step0Labels = mixedMoment B raw25618step1 raw25618step1Labels := by
      have hz : ∀ j, raw25618step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25618step1 = (fun i j => raw25618step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25618step1 raw25618step0; decide +kernel
      have hl : raw25618step1Labels = raw25618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25618step0 raw25618step0Labels permutation56 hz
    mixedMoment B raw25618step1 raw25618step1Labels = mixedMoment B raw25618step2 raw25618step2Labels := by
      have ha : raw25618step2 = (fun i j => raw25618step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25618step2 raw25618step1; decide +kernel
      have hl : raw25618step2Labels = raw25618step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25618step1 raw25618step1Labels permutation11 permutation2
    _ = mixedMoment B node4185 node4185Labels := by rfl

def raw25619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25619 raw25619Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw25619 raw25619Labels = mixedMoment B raw25619step0 raw25619step0Labels := by
      have hz : ∀ j, raw25619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25619step0 = (fun i j => raw25619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25619step0 raw25619; decide +kernel
      have hl : raw25619step0Labels = raw25619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25619 raw25619Labels permutation346 hz
    mixedMoment B raw25619step0 raw25619step0Labels = mixedMoment B raw25619step1 raw25619step1Labels := by
      have ha : raw25619step1 = (fun i j => raw25619step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25619step1 raw25619step0; decide +kernel
      have hl : raw25619step1Labels = raw25619step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25619step0 raw25619step0Labels permutation35 permutation2
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw25620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25620 raw25620Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw25620 raw25620Labels = mixedMoment B raw25620step0 raw25620step0Labels := by
      have hz : ∀ j, raw25620 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25620step0 = (fun i j => raw25620 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25620step0 raw25620; decide +kernel
      have hl : raw25620step0Labels = raw25620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25620 raw25620Labels permutation265 hz
    mixedMoment B raw25620step0 raw25620step0Labels = mixedMoment B raw25620step1 raw25620step1Labels := by
      have ha : raw25620step1 = (fun i j => raw25620step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25620step1 raw25620step0; decide +kernel
      have hl : raw25620step1Labels = raw25620step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25620step0 raw25620step0Labels permutation35 permutation2
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw25621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25621 raw25621Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw25621 raw25621Labels = mixedMoment B raw25621step0 raw25621step0Labels := by
      have hz : ∀ j, raw25621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25621step0 = (fun i j => raw25621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25621step0 raw25621; decide +kernel
      have hl : raw25621step0Labels = raw25621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25621 raw25621Labels permutation346 hz
    mixedMoment B raw25621step0 raw25621step0Labels = mixedMoment B raw25621step1 raw25621step1Labels := by
      have hz : ∀ j, raw25621step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25621step1 = (fun i j => raw25621step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25621step1 raw25621step0; decide +kernel
      have hl : raw25621step1Labels = raw25621step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25621step0 raw25621step0Labels permutation56 hz
    mixedMoment B raw25621step1 raw25621step1Labels = mixedMoment B raw25621step2 raw25621step2Labels := by
      have ha : raw25621step2 = (fun i j => raw25621step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25621step2 raw25621step1; decide +kernel
      have hl : raw25621step2Labels = raw25621step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25621step1 raw25621step1Labels permutation11 permutation2
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw25622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25622step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25622 raw25622Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw25622 raw25622Labels = mixedMoment B raw25622step0 raw25622step0Labels := by
      have hz : ∀ j, raw25622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25622step0 = (fun i j => raw25622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25622step0 raw25622; decide +kernel
      have hl : raw25622step0Labels = raw25622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25622 raw25622Labels permutation346 hz
    mixedMoment B raw25622step0 raw25622step0Labels = mixedMoment B raw25622step1 raw25622step1Labels := by
      have hz : ∀ j, raw25622step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25622step1 = (fun i j => raw25622step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25622step1 raw25622step0; decide +kernel
      have hl : raw25622step1Labels = raw25622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25622step0 raw25622step0Labels permutation56 hz
    mixedMoment B raw25622step1 raw25622step1Labels = mixedMoment B raw25622step2 raw25622step2Labels := by
      have ha : raw25622step2 = (fun i j => raw25622step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25622step2 raw25622step1; decide +kernel
      have hl : raw25622step2Labels = raw25622step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25622step1 raw25622step1Labels permutation13 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw25623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25623 raw25623Labels = mixedMoment B node4188 node4188Labels := by
  calc
    mixedMoment B raw25623 raw25623Labels = mixedMoment B raw25623step0 raw25623step0Labels := by
      have hz : ∀ j, raw25623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25623step0 = (fun i j => raw25623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25623step0 raw25623; decide +kernel
      have hl : raw25623step0Labels = raw25623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25623 raw25623Labels permutation346 hz
    mixedMoment B raw25623step0 raw25623step0Labels = mixedMoment B raw25623step1 raw25623step1Labels := by
      have hz : ∀ j, raw25623step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25623step1 = (fun i j => raw25623step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25623step1 raw25623step0; decide +kernel
      have hl : raw25623step1Labels = raw25623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25623step0 raw25623step0Labels permutation56 hz
    mixedMoment B raw25623step1 raw25623step1Labels = mixedMoment B raw25623step2 raw25623step2Labels := by
      have ha : raw25623step2 = (fun i j => raw25623step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25623step2 raw25623step1; decide +kernel
      have hl : raw25623step2Labels = raw25623step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25623step1 raw25623step1Labels permutation9 permutation2
    _ = mixedMoment B node4188 node4188Labels := by rfl

def raw25624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25624 raw25624Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw25624 raw25624Labels = mixedMoment B raw25624step0 raw25624step0Labels := by
      have hz : ∀ j, raw25624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25624step0 = (fun i j => raw25624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25624step0 raw25624; decide +kernel
      have hl : raw25624step0Labels = raw25624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25624 raw25624Labels permutation346 hz
    mixedMoment B raw25624step0 raw25624step0Labels = mixedMoment B raw25624step1 raw25624step1Labels := by
      have ha : raw25624step1 = (fun i j => raw25624step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25624step1 raw25624step0; decide +kernel
      have hl : raw25624step1Labels = raw25624step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25624step0 raw25624step0Labels permutation33 permutation2
    _ = mixedMoment B node4357 node4357Labels := by rfl

def raw25625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25625 raw25625Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw25625 raw25625Labels = mixedMoment B raw25625step0 raw25625step0Labels := by
      have hz : ∀ j, raw25625 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25625step0 = (fun i j => raw25625 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25625step0 raw25625; decide +kernel
      have hl : raw25625step0Labels = raw25625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25625 raw25625Labels permutation265 hz
    mixedMoment B raw25625step0 raw25625step0Labels = mixedMoment B raw25625step1 raw25625step1Labels := by
      have ha : raw25625step1 = (fun i j => raw25625step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25625step1 raw25625step0; decide +kernel
      have hl : raw25625step1Labels = raw25625step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25625step0 raw25625step0Labels permutation33 permutation2
    _ = mixedMoment B node4357 node4357Labels := by rfl

def raw25626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25626step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25626 raw25626Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw25626 raw25626Labels = mixedMoment B raw25626step0 raw25626step0Labels := by
      have hz : ∀ j, raw25626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25626step0 = (fun i j => raw25626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25626step0 raw25626; decide +kernel
      have hl : raw25626step0Labels = raw25626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25626 raw25626Labels permutation346 hz
    mixedMoment B raw25626step0 raw25626step0Labels = mixedMoment B raw25626step1 raw25626step1Labels := by
      have hz : ∀ j, raw25626step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25626step1 = (fun i j => raw25626step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25626step1 raw25626step0; decide +kernel
      have hl : raw25626step1Labels = raw25626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25626step0 raw25626step0Labels permutation56 hz
    mixedMoment B raw25626step1 raw25626step1Labels = mixedMoment B raw25626step2 raw25626step2Labels := by
      have ha : raw25626step2 = (fun i j => raw25626step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25626step2 raw25626step1; decide +kernel
      have hl : raw25626step2Labels = raw25626step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25626step1 raw25626step1Labels permutation9 permutation2
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw25627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25627 raw25627Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw25627 raw25627Labels = mixedMoment B raw25627step0 raw25627step0Labels := by
      have hz : ∀ j, raw25627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25627step0 = (fun i j => raw25627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25627step0 raw25627; decide +kernel
      have hl : raw25627step0Labels = raw25627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25627 raw25627Labels permutation346 hz
    mixedMoment B raw25627step0 raw25627step0Labels = mixedMoment B raw25627step1 raw25627step1Labels := by
      have hz : ∀ j, raw25627step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25627step1 = (fun i j => raw25627step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25627step1 raw25627step0; decide +kernel
      have hl : raw25627step1Labels = raw25627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25627step0 raw25627step0Labels permutation56 hz
    mixedMoment B raw25627step1 raw25627step1Labels = mixedMoment B raw25627step2 raw25627step2Labels := by
      have ha : raw25627step2 = (fun i j => raw25627step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25627step2 raw25627step1; decide +kernel
      have hl : raw25627step2Labels = raw25627step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25627step1 raw25627step1Labels permutation12 permutation2
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw25628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25628 raw25628Labels = mixedMoment B node4184 node4184Labels := by
  calc
    mixedMoment B raw25628 raw25628Labels = mixedMoment B raw25628step0 raw25628step0Labels := by
      have hz : ∀ j, raw25628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25628step0 = (fun i j => raw25628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25628step0 raw25628; decide +kernel
      have hl : raw25628step0Labels = raw25628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25628 raw25628Labels permutation346 hz
    mixedMoment B raw25628step0 raw25628step0Labels = mixedMoment B raw25628step1 raw25628step1Labels := by
      have hz : ∀ j, raw25628step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25628step1 = (fun i j => raw25628step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25628step1 raw25628step0; decide +kernel
      have hl : raw25628step1Labels = raw25628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25628step0 raw25628step0Labels permutation56 hz
    mixedMoment B raw25628step1 raw25628step1Labels = mixedMoment B raw25628step2 raw25628step2Labels := by
      have ha : raw25628step2 = (fun i j => raw25628step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25628step2 raw25628step1; decide +kernel
      have hl : raw25628step2Labels = raw25628step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25628step1 raw25628step1Labels permutation10 permutation2
    _ = mixedMoment B node4184 node4184Labels := by rfl

def raw25629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25629 raw25629Labels = mixedMoment B node4353 node4353Labels := by
  calc
    mixedMoment B raw25629 raw25629Labels = mixedMoment B raw25629step0 raw25629step0Labels := by
      have hz : ∀ j, raw25629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25629step0 = (fun i j => raw25629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25629step0 raw25629; decide +kernel
      have hl : raw25629step0Labels = raw25629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25629 raw25629Labels permutation346 hz
    mixedMoment B raw25629step0 raw25629step0Labels = mixedMoment B raw25629step1 raw25629step1Labels := by
      have ha : raw25629step1 = (fun i j => raw25629step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25629step1 raw25629step0; decide +kernel
      have hl : raw25629step1Labels = raw25629step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25629step0 raw25629step0Labels permutation34 permutation2
    _ = mixedMoment B node4353 node4353Labels := by rfl

def raw25630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25630step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25630 raw25630Labels = mixedMoment B node4353 node4353Labels := by
  calc
    mixedMoment B raw25630 raw25630Labels = mixedMoment B raw25630step0 raw25630step0Labels := by
      have hz : ∀ j, raw25630 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25630step0 = (fun i j => raw25630 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25630step0 raw25630; decide +kernel
      have hl : raw25630step0Labels = raw25630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25630 raw25630Labels permutation265 hz
    mixedMoment B raw25630step0 raw25630step0Labels = mixedMoment B raw25630step1 raw25630step1Labels := by
      have ha : raw25630step1 = (fun i j => raw25630step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25630step1 raw25630step0; decide +kernel
      have hl : raw25630step1Labels = raw25630step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25630step0 raw25630step0Labels permutation34 permutation2
    _ = mixedMoment B node4353 node4353Labels := by rfl

def raw25631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25631 raw25631Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw25631 raw25631Labels = mixedMoment B raw25631step0 raw25631step0Labels := by
      have hz : ∀ j, raw25631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25631step0 = (fun i j => raw25631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25631step0 raw25631; decide +kernel
      have hl : raw25631step0Labels = raw25631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25631 raw25631Labels permutation346 hz
    mixedMoment B raw25631step0 raw25631step0Labels = mixedMoment B raw25631step1 raw25631step1Labels := by
      have hz : ∀ j, raw25631step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25631step1 = (fun i j => raw25631step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25631step1 raw25631step0; decide +kernel
      have hl : raw25631step1Labels = raw25631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25631step0 raw25631step0Labels permutation56 hz
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw25632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25632step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25632 raw25632Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw25632 raw25632Labels = mixedMoment B raw25632step0 raw25632step0Labels := by
      have hz : ∀ j, raw25632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25632step0 = (fun i j => raw25632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25632step0 raw25632; decide +kernel
      have hl : raw25632step0Labels = raw25632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25632 raw25632Labels permutation346 hz
    mixedMoment B raw25632step0 raw25632step0Labels = mixedMoment B raw25632step1 raw25632step1Labels := by
      have hz : ∀ j, raw25632step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25632step1 = (fun i j => raw25632step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25632step1 raw25632step0; decide +kernel
      have hl : raw25632step1Labels = raw25632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25632step0 raw25632step0Labels permutation56 hz
    mixedMoment B raw25632step1 raw25632step1Labels = mixedMoment B raw25632step2 raw25632step2Labels := by
      have ha : raw25632step2 = (fun i j => raw25632step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25632step2 raw25632step1; decide +kernel
      have hl : raw25632step2Labels = raw25632step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25632step1 raw25632step1Labels permutation10 permutation2
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw25633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25633step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25633step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25633 raw25633Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw25633 raw25633Labels = mixedMoment B raw25633step0 raw25633step0Labels := by
      have hz : ∀ j, raw25633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25633step0 = (fun i j => raw25633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25633step0 raw25633; decide +kernel
      have hl : raw25633step0Labels = raw25633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25633 raw25633Labels permutation346 hz
    mixedMoment B raw25633step0 raw25633step0Labels = mixedMoment B raw25633step1 raw25633step1Labels := by
      have ha : raw25633step1 = (fun i j => raw25633step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25633step1 raw25633step0; decide +kernel
      have hl : raw25633step1Labels = raw25633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25633step0 raw25633step0Labels permutation37 permutation7
    mixedMoment B raw25633step1 raw25633step1Labels = mixedMoment B raw25633step2 raw25633step2Labels := by
      have ha : raw25633step2 = -raw25633step1 := by apply Matrix.ext; change ∀ i j, raw25633step2 i j = -(raw25633step1 i j); unfold raw25633step2 raw25633step1; decide +kernel
      have hl : raw25633step2Labels = raw25633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25633step2 raw25633step2Labels = mixedMoment B raw25633step3 raw25633step3Labels := by
      have ha : raw25633step3 = raw25633step2 := by apply Matrix.ext; unfold raw25633step3 raw25633step2; decide +kernel
      have hl : raw25633step2Labels = labelEmbedding1 ∘ raw25633step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25633step2 raw25633step2Labels raw25633step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw25634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25634step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25634step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25634step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25634 raw25634Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw25634 raw25634Labels = mixedMoment B raw25634step0 raw25634step0Labels := by
      have hz : ∀ j, raw25634 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25634step0 = (fun i j => raw25634 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25634step0 raw25634; decide +kernel
      have hl : raw25634step0Labels = raw25634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25634 raw25634Labels permutation265 hz
    mixedMoment B raw25634step0 raw25634step0Labels = mixedMoment B raw25634step1 raw25634step1Labels := by
      have ha : raw25634step1 = (fun i j => raw25634step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25634step1 raw25634step0; decide +kernel
      have hl : raw25634step1Labels = raw25634step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25634step0 raw25634step0Labels permutation37 permutation7
    mixedMoment B raw25634step1 raw25634step1Labels = mixedMoment B raw25634step2 raw25634step2Labels := by
      have ha : raw25634step2 = -raw25634step1 := by apply Matrix.ext; change ∀ i j, raw25634step2 i j = -(raw25634step1 i j); unfold raw25634step2 raw25634step1; decide +kernel
      have hl : raw25634step2Labels = raw25634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25634step2 raw25634step2Labels = mixedMoment B raw25634step3 raw25634step3Labels := by
      have ha : raw25634step3 = raw25634step2 := by apply Matrix.ext; unfold raw25634step3 raw25634step2; decide +kernel
      have hl : raw25634step2Labels = labelEmbedding1 ∘ raw25634step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25634step2 raw25634step2Labels raw25634step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw25635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw25635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25635step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25635 raw25635Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw25635 raw25635Labels = mixedMoment B raw25635step0 raw25635step0Labels := by
      have hz : ∀ j, raw25635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25635step0 = (fun i j => raw25635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25635step0 raw25635; decide +kernel
      have hl : raw25635step0Labels = raw25635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25635 raw25635Labels permutation346 hz
    mixedMoment B raw25635step0 raw25635step0Labels = mixedMoment B raw25635step1 raw25635step1Labels := by
      have hz : ∀ j, raw25635step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25635step1 = (fun i j => raw25635step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25635step1 raw25635step0; decide +kernel
      have hl : raw25635step1Labels = raw25635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25635step0 raw25635step0Labels permutation56 hz
    mixedMoment B raw25635step1 raw25635step1Labels = mixedMoment B raw25635step2 raw25635step2Labels := by
      have ha : raw25635step2 = (fun i j => raw25635step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25635step2 raw25635step1; decide +kernel
      have hl : raw25635step2Labels = raw25635step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25635step1 raw25635step1Labels permutation13 permutation7
    mixedMoment B raw25635step2 raw25635step2Labels = mixedMoment B raw25635step3 raw25635step3Labels := by
      have ha : raw25635step3 = -raw25635step2 := by apply Matrix.ext; change ∀ i j, raw25635step3 i j = -(raw25635step2 i j); unfold raw25635step3 raw25635step2; decide +kernel
      have hl : raw25635step3Labels = raw25635step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25635step3 raw25635step3Labels = mixedMoment B raw25635step4 raw25635step4Labels := by
      have ha : raw25635step4 = raw25635step3 := by apply Matrix.ext; unfold raw25635step4 raw25635step3; decide +kernel
      have hl : raw25635step3Labels = labelEmbedding1 ∘ raw25635step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25635step3 raw25635step3Labels raw25635step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw25636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25636step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25636step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25636step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25636step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25636step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25636 raw25636Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw25636 raw25636Labels = mixedMoment B raw25636step0 raw25636step0Labels := by
      have hz : ∀ j, raw25636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25636step0 = (fun i j => raw25636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25636step0 raw25636; decide +kernel
      have hl : raw25636step0Labels = raw25636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25636 raw25636Labels permutation346 hz
    mixedMoment B raw25636step0 raw25636step0Labels = mixedMoment B raw25636step1 raw25636step1Labels := by
      have hz : ∀ j, raw25636step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25636step1 = (fun i j => raw25636step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25636step1 raw25636step0; decide +kernel
      have hl : raw25636step1Labels = raw25636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25636step0 raw25636step0Labels permutation56 hz
    mixedMoment B raw25636step1 raw25636step1Labels = mixedMoment B raw25636step2 raw25636step2Labels := by
      have ha : raw25636step2 = (fun i j => raw25636step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25636step2 raw25636step1; decide +kernel
      have hl : raw25636step2Labels = raw25636step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25636step1 raw25636step1Labels permutation13 permutation7
    mixedMoment B raw25636step2 raw25636step2Labels = mixedMoment B raw25636step3 raw25636step3Labels := by
      have ha : raw25636step3 = -raw25636step2 := by apply Matrix.ext; change ∀ i j, raw25636step3 i j = -(raw25636step2 i j); unfold raw25636step3 raw25636step2; decide +kernel
      have hl : raw25636step3Labels = raw25636step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25636step3 raw25636step3Labels = mixedMoment B raw25636step4 raw25636step4Labels := by
      have ha : raw25636step4 = raw25636step3 := by apply Matrix.ext; unfold raw25636step4 raw25636step3; decide +kernel
      have hl : raw25636step3Labels = labelEmbedding1 ∘ raw25636step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25636step3 raw25636step3Labels raw25636step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw25637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25637step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25637step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25637step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25637step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25637step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25637 raw25637Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw25637 raw25637Labels = mixedMoment B raw25637step0 raw25637step0Labels := by
      have hz : ∀ j, raw25637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25637step0 = (fun i j => raw25637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25637step0 raw25637; decide +kernel
      have hl : raw25637step0Labels = raw25637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25637 raw25637Labels permutation346 hz
    mixedMoment B raw25637step0 raw25637step0Labels = mixedMoment B raw25637step1 raw25637step1Labels := by
      have hz : ∀ j, raw25637step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25637step1 = (fun i j => raw25637step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25637step1 raw25637step0; decide +kernel
      have hl : raw25637step1Labels = raw25637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25637step0 raw25637step0Labels permutation56 hz
    mixedMoment B raw25637step1 raw25637step1Labels = mixedMoment B raw25637step2 raw25637step2Labels := by
      have ha : raw25637step2 = (fun i j => raw25637step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25637step2 raw25637step1; decide +kernel
      have hl : raw25637step2Labels = raw25637step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25637step1 raw25637step1Labels permutation13 permutation7
    mixedMoment B raw25637step2 raw25637step2Labels = mixedMoment B raw25637step3 raw25637step3Labels := by
      have ha : raw25637step3 = -raw25637step2 := by apply Matrix.ext; change ∀ i j, raw25637step3 i j = -(raw25637step2 i j); unfold raw25637step3 raw25637step2; decide +kernel
      have hl : raw25637step3Labels = raw25637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25637step3 raw25637step3Labels = mixedMoment B raw25637step4 raw25637step4Labels := by
      have ha : raw25637step4 = raw25637step3 := by apply Matrix.ext; unfold raw25637step4 raw25637step3; decide +kernel
      have hl : raw25637step3Labels = labelEmbedding1 ∘ raw25637step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25637step3 raw25637step3Labels raw25637step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw25638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25638step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25638step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25638 raw25638Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw25638 raw25638Labels = mixedMoment B raw25638step0 raw25638step0Labels := by
      have hz : ∀ j, raw25638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25638step0 = (fun i j => raw25638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25638step0 raw25638; decide +kernel
      have hl : raw25638step0Labels = raw25638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25638 raw25638Labels permutation346 hz
    mixedMoment B raw25638step0 raw25638step0Labels = mixedMoment B raw25638step1 raw25638step1Labels := by
      have ha : raw25638step1 = (fun i j => raw25638step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25638step1 raw25638step0; decide +kernel
      have hl : raw25638step1Labels = raw25638step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25638step0 raw25638step0Labels permutation37 permutation7
    mixedMoment B raw25638step1 raw25638step1Labels = mixedMoment B raw25638step2 raw25638step2Labels := by
      have ha : raw25638step2 = -raw25638step1 := by apply Matrix.ext; change ∀ i j, raw25638step2 i j = -(raw25638step1 i j); unfold raw25638step2 raw25638step1; decide +kernel
      have hl : raw25638step2Labels = raw25638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25638step2 raw25638step2Labels = mixedMoment B raw25638step3 raw25638step3Labels := by
      have ha : raw25638step3 = raw25638step2 := by apply Matrix.ext; unfold raw25638step3 raw25638step2; decide +kernel
      have hl : raw25638step2Labels = labelEmbedding1 ∘ raw25638step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25638step2 raw25638step2Labels raw25638step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

def raw25639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25639step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25639step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25639step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25639 raw25639Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw25639 raw25639Labels = mixedMoment B raw25639step0 raw25639step0Labels := by
      have ha : raw25639step0 = (fun i j => raw25639 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25639step0 raw25639; decide +kernel
      have hl : raw25639step0Labels = raw25639Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25639 raw25639Labels permutation181 permutation7
    mixedMoment B raw25639step0 raw25639step0Labels = mixedMoment B raw25639step1 raw25639step1Labels := by
      have ha : raw25639step1 = -raw25639step0 := by apply Matrix.ext; change ∀ i j, raw25639step1 i j = -(raw25639step0 i j); unfold raw25639step1 raw25639step0; decide +kernel
      have hl : raw25639step1Labels = raw25639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25639step1 raw25639step1Labels = mixedMoment B raw25639step2 raw25639step2Labels := by
      have ha : raw25639step2 = raw25639step1 := by apply Matrix.ext; unfold raw25639step2 raw25639step1; decide +kernel
      have hl : raw25639step1Labels = labelEmbedding1 ∘ raw25639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25639step1 raw25639step1Labels raw25639step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

def raw25640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw25640step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25640step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25640 raw25640Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw25640 raw25640Labels = mixedMoment B raw25640step0 raw25640step0Labels := by
      have hz : ∀ j, raw25640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25640step0 = (fun i j => raw25640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25640step0 raw25640; decide +kernel
      have hl : raw25640step0Labels = raw25640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25640 raw25640Labels permutation346 hz
    mixedMoment B raw25640step0 raw25640step0Labels = mixedMoment B raw25640step1 raw25640step1Labels := by
      have ha : raw25640step1 = (fun i j => raw25640step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25640step1 raw25640step0; decide +kernel
      have hl : raw25640step1Labels = raw25640step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25640step0 raw25640step0Labels permutation37 permutation7
    mixedMoment B raw25640step1 raw25640step1Labels = mixedMoment B raw25640step2 raw25640step2Labels := by
      have ha : raw25640step2 = -raw25640step1 := by apply Matrix.ext; change ∀ i j, raw25640step2 i j = -(raw25640step1 i j); unfold raw25640step2 raw25640step1; decide +kernel
      have hl : raw25640step2Labels = raw25640step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25640step2 raw25640step2Labels = mixedMoment B raw25640step3 raw25640step3Labels := by
      have ha : raw25640step3 = raw25640step2 := by apply Matrix.ext; unfold raw25640step3 raw25640step2; decide +kernel
      have hl : raw25640step2Labels = labelEmbedding1 ∘ raw25640step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25640step2 raw25640step2Labels raw25640step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw25641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25641step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25641step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25641step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25641step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25641step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25641 raw25641Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw25641 raw25641Labels = mixedMoment B raw25641step0 raw25641step0Labels := by
      have hz : ∀ j, raw25641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25641step0 = (fun i j => raw25641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25641step0 raw25641; decide +kernel
      have hl : raw25641step0Labels = raw25641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25641 raw25641Labels permutation346 hz
    mixedMoment B raw25641step0 raw25641step0Labels = mixedMoment B raw25641step1 raw25641step1Labels := by
      have ha : raw25641step1 = (fun i j => raw25641step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25641step1 raw25641step0; decide +kernel
      have hl : raw25641step1Labels = raw25641step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25641step0 raw25641step0Labels permutation37 permutation7
    mixedMoment B raw25641step1 raw25641step1Labels = mixedMoment B raw25641step2 raw25641step2Labels := by
      have ha : raw25641step2 = -raw25641step1 := by apply Matrix.ext; change ∀ i j, raw25641step2 i j = -(raw25641step1 i j); unfold raw25641step2 raw25641step1; decide +kernel
      have hl : raw25641step2Labels = raw25641step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25641step2 raw25641step2Labels = mixedMoment B raw25641step3 raw25641step3Labels := by
      have ha : raw25641step3 = raw25641step2 := by apply Matrix.ext; unfold raw25641step3 raw25641step2; decide +kernel
      have hl : raw25641step2Labels = labelEmbedding1 ∘ raw25641step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25641step2 raw25641step2Labels raw25641step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw25642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25642step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25642step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25642 raw25642Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw25642 raw25642Labels = mixedMoment B raw25642step0 raw25642step0Labels := by
      have hz : ∀ j, raw25642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25642step0 = (fun i j => raw25642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25642step0 raw25642; decide +kernel
      have hl : raw25642step0Labels = raw25642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25642 raw25642Labels permutation346 hz
    mixedMoment B raw25642step0 raw25642step0Labels = mixedMoment B raw25642step1 raw25642step1Labels := by
      have ha : raw25642step1 = (fun i j => raw25642step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25642step1 raw25642step0; decide +kernel
      have hl : raw25642step1Labels = raw25642step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25642step0 raw25642step0Labels permutation37 permutation7
    mixedMoment B raw25642step1 raw25642step1Labels = mixedMoment B raw25642step2 raw25642step2Labels := by
      have ha : raw25642step2 = -raw25642step1 := by apply Matrix.ext; change ∀ i j, raw25642step2 i j = -(raw25642step1 i j); unfold raw25642step2 raw25642step1; decide +kernel
      have hl : raw25642step2Labels = raw25642step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25642step2 raw25642step2Labels = mixedMoment B raw25642step3 raw25642step3Labels := by
      have ha : raw25642step3 = raw25642step2 := by apply Matrix.ext; unfold raw25642step3 raw25642step2; decide +kernel
      have hl : raw25642step2Labels = labelEmbedding1 ∘ raw25642step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25642step2 raw25642step2Labels raw25642step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw25643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25643step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25643step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25643step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25643 raw25643Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw25643 raw25643Labels = mixedMoment B raw25643step0 raw25643step0Labels := by
      have hz : ∀ j, raw25643 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25643step0 = (fun i j => raw25643 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25643step0 raw25643; decide +kernel
      have hl : raw25643step0Labels = raw25643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25643 raw25643Labels permutation265 hz
    mixedMoment B raw25643step0 raw25643step0Labels = mixedMoment B raw25643step1 raw25643step1Labels := by
      have ha : raw25643step1 = (fun i j => raw25643step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25643step1 raw25643step0; decide +kernel
      have hl : raw25643step1Labels = raw25643step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25643step0 raw25643step0Labels permutation37 permutation7
    mixedMoment B raw25643step1 raw25643step1Labels = mixedMoment B raw25643step2 raw25643step2Labels := by
      have ha : raw25643step2 = -raw25643step1 := by apply Matrix.ext; change ∀ i j, raw25643step2 i j = -(raw25643step1 i j); unfold raw25643step2 raw25643step1; decide +kernel
      have hl : raw25643step2Labels = raw25643step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25643step2 raw25643step2Labels = mixedMoment B raw25643step3 raw25643step3Labels := by
      have ha : raw25643step3 = raw25643step2 := by apply Matrix.ext; unfold raw25643step3 raw25643step2; decide +kernel
      have hl : raw25643step2Labels = labelEmbedding1 ∘ raw25643step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25643step2 raw25643step2Labels raw25643step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

def raw25644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25644step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25644step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25644 raw25644Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw25644 raw25644Labels = mixedMoment B raw25644step0 raw25644step0Labels := by
      have ha : raw25644step0 = (fun i j => raw25644 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25644step0 raw25644; decide +kernel
      have hl : raw25644step0Labels = raw25644Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25644 raw25644Labels permutation157 permutation7
    mixedMoment B raw25644step0 raw25644step0Labels = mixedMoment B raw25644step1 raw25644step1Labels := by
      have ha : raw25644step1 = -raw25644step0 := by apply Matrix.ext; change ∀ i j, raw25644step1 i j = -(raw25644step0 i j); unfold raw25644step1 raw25644step0; decide +kernel
      have hl : raw25644step1Labels = raw25644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25644step1 raw25644step1Labels = mixedMoment B raw25644step2 raw25644step2Labels := by
      have ha : raw25644step2 = raw25644step1 := by apply Matrix.ext; unfold raw25644step2 raw25644step1; decide +kernel
      have hl : raw25644step1Labels = labelEmbedding1 ∘ raw25644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25644step1 raw25644step1Labels raw25644step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

def raw25645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw25645step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25645step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25645 raw25645Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw25645 raw25645Labels = mixedMoment B raw25645step0 raw25645step0Labels := by
      have hz : ∀ j, raw25645 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25645step0 = (fun i j => raw25645 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25645step0 raw25645; decide +kernel
      have hl : raw25645step0Labels = raw25645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25645 raw25645Labels permutation265 hz
    mixedMoment B raw25645step0 raw25645step0Labels = mixedMoment B raw25645step1 raw25645step1Labels := by
      have ha : raw25645step1 = (fun i j => raw25645step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25645step1 raw25645step0; decide +kernel
      have hl : raw25645step1Labels = raw25645step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25645step0 raw25645step0Labels permutation37 permutation7
    mixedMoment B raw25645step1 raw25645step1Labels = mixedMoment B raw25645step2 raw25645step2Labels := by
      have ha : raw25645step2 = -raw25645step1 := by apply Matrix.ext; change ∀ i j, raw25645step2 i j = -(raw25645step1 i j); unfold raw25645step2 raw25645step1; decide +kernel
      have hl : raw25645step2Labels = raw25645step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25645step2 raw25645step2Labels = mixedMoment B raw25645step3 raw25645step3Labels := by
      have ha : raw25645step3 = raw25645step2 := by apply Matrix.ext; unfold raw25645step3 raw25645step2; decide +kernel
      have hl : raw25645step2Labels = labelEmbedding1 ∘ raw25645step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25645step2 raw25645step2Labels raw25645step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw25646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25646step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25646step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25646step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25646step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25646 raw25646Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw25646 raw25646Labels = mixedMoment B raw25646step0 raw25646step0Labels := by
      have hz : ∀ j, raw25646 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25646step0 = (fun i j => raw25646 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25646step0 raw25646; decide +kernel
      have hl : raw25646step0Labels = raw25646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25646 raw25646Labels permutation265 hz
    mixedMoment B raw25646step0 raw25646step0Labels = mixedMoment B raw25646step1 raw25646step1Labels := by
      have ha : raw25646step1 = (fun i j => raw25646step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25646step1 raw25646step0; decide +kernel
      have hl : raw25646step1Labels = raw25646step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25646step0 raw25646step0Labels permutation37 permutation7
    mixedMoment B raw25646step1 raw25646step1Labels = mixedMoment B raw25646step2 raw25646step2Labels := by
      have ha : raw25646step2 = -raw25646step1 := by apply Matrix.ext; change ∀ i j, raw25646step2 i j = -(raw25646step1 i j); unfold raw25646step2 raw25646step1; decide +kernel
      have hl : raw25646step2Labels = raw25646step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25646step2 raw25646step2Labels = mixedMoment B raw25646step3 raw25646step3Labels := by
      have ha : raw25646step3 = raw25646step2 := by apply Matrix.ext; unfold raw25646step3 raw25646step2; decide +kernel
      have hl : raw25646step2Labels = labelEmbedding1 ∘ raw25646step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25646step2 raw25646step2Labels raw25646step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw25647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25647Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25647step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25647step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25647step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25647step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25647step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25647 raw25647Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw25647 raw25647Labels = mixedMoment B raw25647step0 raw25647step0Labels := by
      have hz : ∀ j, raw25647 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25647step0 = (fun i j => raw25647 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25647step0 raw25647; decide +kernel
      have hl : raw25647step0Labels = raw25647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25647 raw25647Labels permutation265 hz
    mixedMoment B raw25647step0 raw25647step0Labels = mixedMoment B raw25647step1 raw25647step1Labels := by
      have ha : raw25647step1 = (fun i j => raw25647step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25647step1 raw25647step0; decide +kernel
      have hl : raw25647step1Labels = raw25647step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25647step0 raw25647step0Labels permutation37 permutation7
    mixedMoment B raw25647step1 raw25647step1Labels = mixedMoment B raw25647step2 raw25647step2Labels := by
      have ha : raw25647step2 = -raw25647step1 := by apply Matrix.ext; change ∀ i j, raw25647step2 i j = -(raw25647step1 i j); unfold raw25647step2 raw25647step1; decide +kernel
      have hl : raw25647step2Labels = raw25647step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25647step2 raw25647step2Labels = mixedMoment B raw25647step3 raw25647step3Labels := by
      have ha : raw25647step3 = raw25647step2 := by apply Matrix.ext; unfold raw25647step3 raw25647step2; decide +kernel
      have hl : raw25647step2Labels = labelEmbedding1 ∘ raw25647step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25647step2 raw25647step2Labels raw25647step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw25648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25648step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25648step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw25648step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25648step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25648step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25648step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25648 raw25648Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw25648 raw25648Labels = mixedMoment B raw25648step0 raw25648step0Labels := by
      have hz : ∀ j, raw25648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25648step0 = (fun i j => raw25648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25648step0 raw25648; decide +kernel
      have hl : raw25648step0Labels = raw25648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25648 raw25648Labels permutation346 hz
    mixedMoment B raw25648step0 raw25648step0Labels = mixedMoment B raw25648step1 raw25648step1Labels := by
      have hz : ∀ j, raw25648step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25648step1 = (fun i j => raw25648step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25648step1 raw25648step0; decide +kernel
      have hl : raw25648step1Labels = raw25648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25648step0 raw25648step0Labels permutation56 hz
    mixedMoment B raw25648step1 raw25648step1Labels = mixedMoment B raw25648step2 raw25648step2Labels := by
      have ha : raw25648step2 = (fun i j => raw25648step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25648step2 raw25648step1; decide +kernel
      have hl : raw25648step2Labels = raw25648step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25648step1 raw25648step1Labels permutation13 permutation7
    mixedMoment B raw25648step2 raw25648step2Labels = mixedMoment B raw25648step3 raw25648step3Labels := by
      have ha : raw25648step3 = -raw25648step2 := by apply Matrix.ext; change ∀ i j, raw25648step3 i j = -(raw25648step2 i j); unfold raw25648step3 raw25648step2; decide +kernel
      have hl : raw25648step3Labels = raw25648step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25648step3 raw25648step3Labels = mixedMoment B raw25648step4 raw25648step4Labels := by
      have ha : raw25648step4 = raw25648step3 := by apply Matrix.ext; unfold raw25648step4 raw25648step3; decide +kernel
      have hl : raw25648step3Labels = labelEmbedding1 ∘ raw25648step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25648step3 raw25648step3Labels raw25648step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1525 node1525Labels := by rfl

def raw25649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25649Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25649step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw25649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25649step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25649step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25649step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25649 raw25649Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw25649 raw25649Labels = mixedMoment B raw25649step0 raw25649step0Labels := by
      have hz : ∀ j, raw25649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25649step0 = (fun i j => raw25649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25649step0 raw25649; decide +kernel
      have hl : raw25649step0Labels = raw25649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25649 raw25649Labels permutation346 hz
    mixedMoment B raw25649step0 raw25649step0Labels = mixedMoment B raw25649step1 raw25649step1Labels := by
      have ha : raw25649step1 = (fun i j => raw25649step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25649step1 raw25649step0; decide +kernel
      have hl : raw25649step1Labels = raw25649step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25649step0 raw25649step0Labels permutation37 permutation7
    mixedMoment B raw25649step1 raw25649step1Labels = mixedMoment B raw25649step2 raw25649step2Labels := by
      have ha : raw25649step2 = -raw25649step1 := by apply Matrix.ext; change ∀ i j, raw25649step2 i j = -(raw25649step1 i j); unfold raw25649step2 raw25649step1; decide +kernel
      have hl : raw25649step2Labels = raw25649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25649step2 raw25649step2Labels = mixedMoment B raw25649step3 raw25649step3Labels := by
      have ha : raw25649step3 = raw25649step2 := by apply Matrix.ext; unfold raw25649step3 raw25649step2; decide +kernel
      have hl : raw25649step2Labels = labelEmbedding1 ∘ raw25649step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25649step2 raw25649step2Labels raw25649step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

def raw25650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25650Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25650step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw25650step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25650step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25650step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25650step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25650 raw25650Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw25650 raw25650Labels = mixedMoment B raw25650step0 raw25650step0Labels := by
      have hz : ∀ j, raw25650 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25650step0 = (fun i j => raw25650 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25650step0 raw25650; decide +kernel
      have hl : raw25650step0Labels = raw25650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25650 raw25650Labels permutation265 hz
    mixedMoment B raw25650step0 raw25650step0Labels = mixedMoment B raw25650step1 raw25650step1Labels := by
      have ha : raw25650step1 = (fun i j => raw25650step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25650step1 raw25650step0; decide +kernel
      have hl : raw25650step1Labels = raw25650step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25650step0 raw25650step0Labels permutation37 permutation7
    mixedMoment B raw25650step1 raw25650step1Labels = mixedMoment B raw25650step2 raw25650step2Labels := by
      have ha : raw25650step2 = -raw25650step1 := by apply Matrix.ext; change ∀ i j, raw25650step2 i j = -(raw25650step1 i j); unfold raw25650step2 raw25650step1; decide +kernel
      have hl : raw25650step2Labels = raw25650step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25650step2 raw25650step2Labels = mixedMoment B raw25650step3 raw25650step3Labels := by
      have ha : raw25650step3 = raw25650step2 := by apply Matrix.ext; unfold raw25650step3 raw25650step2; decide +kernel
      have hl : raw25650step2Labels = labelEmbedding1 ∘ raw25650step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25650step2 raw25650step2Labels raw25650step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

def raw25651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25651Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25651step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25651step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25651step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25651step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25651step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25651step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25651 raw25651Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw25651 raw25651Labels = mixedMoment B raw25651step0 raw25651step0Labels := by
      have hz : ∀ j, raw25651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25651step0 = (fun i j => raw25651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25651step0 raw25651; decide +kernel
      have hl : raw25651step0Labels = raw25651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25651 raw25651Labels permutation346 hz
    mixedMoment B raw25651step0 raw25651step0Labels = mixedMoment B raw25651step1 raw25651step1Labels := by
      have hz : ∀ j, raw25651step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25651step1 = (fun i j => raw25651step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25651step1 raw25651step0; decide +kernel
      have hl : raw25651step1Labels = raw25651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25651step0 raw25651step0Labels permutation56 hz
    mixedMoment B raw25651step1 raw25651step1Labels = mixedMoment B raw25651step2 raw25651step2Labels := by
      have ha : raw25651step2 = (fun i j => raw25651step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25651step2 raw25651step1; decide +kernel
      have hl : raw25651step2Labels = raw25651step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25651step1 raw25651step1Labels permutation13 permutation7
    mixedMoment B raw25651step2 raw25651step2Labels = mixedMoment B raw25651step3 raw25651step3Labels := by
      have ha : raw25651step3 = -raw25651step2 := by apply Matrix.ext; change ∀ i j, raw25651step3 i j = -(raw25651step2 i j); unfold raw25651step3 raw25651step2; decide +kernel
      have hl : raw25651step3Labels = raw25651step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25651step3 raw25651step3Labels = mixedMoment B raw25651step4 raw25651step4Labels := by
      have ha : raw25651step4 = raw25651step3 := by apply Matrix.ext; unfold raw25651step4 raw25651step3; decide +kernel
      have hl : raw25651step3Labels = labelEmbedding1 ∘ raw25651step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25651step3 raw25651step3Labels raw25651step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw25652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25652Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25652step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25652step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25652step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25652step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25652step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25652step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25652step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25652 raw25652Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw25652 raw25652Labels = mixedMoment B raw25652step0 raw25652step0Labels := by
      have hz : ∀ j, raw25652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25652step0 = (fun i j => raw25652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25652step0 raw25652; decide +kernel
      have hl : raw25652step0Labels = raw25652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25652 raw25652Labels permutation346 hz
    mixedMoment B raw25652step0 raw25652step0Labels = mixedMoment B raw25652step1 raw25652step1Labels := by
      have hz : ∀ j, raw25652step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25652step1 = (fun i j => raw25652step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25652step1 raw25652step0; decide +kernel
      have hl : raw25652step1Labels = raw25652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25652step0 raw25652step0Labels permutation56 hz
    mixedMoment B raw25652step1 raw25652step1Labels = mixedMoment B raw25652step2 raw25652step2Labels := by
      have ha : raw25652step2 = (fun i j => raw25652step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25652step2 raw25652step1; decide +kernel
      have hl : raw25652step2Labels = raw25652step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25652step1 raw25652step1Labels permutation13 permutation7
    mixedMoment B raw25652step2 raw25652step2Labels = mixedMoment B raw25652step3 raw25652step3Labels := by
      have ha : raw25652step3 = -raw25652step2 := by apply Matrix.ext; change ∀ i j, raw25652step3 i j = -(raw25652step2 i j); unfold raw25652step3 raw25652step2; decide +kernel
      have hl : raw25652step3Labels = raw25652step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25652step3 raw25652step3Labels = mixedMoment B raw25652step4 raw25652step4Labels := by
      have ha : raw25652step4 = raw25652step3 := by apply Matrix.ext; unfold raw25652step4 raw25652step3; decide +kernel
      have hl : raw25652step3Labels = labelEmbedding1 ∘ raw25652step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25652step3 raw25652step3Labels raw25652step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw25653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25653Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25653step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25653step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25653step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25653step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25653step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25653step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25653step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25653step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25653 raw25653Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw25653 raw25653Labels = mixedMoment B raw25653step0 raw25653step0Labels := by
      have hz : ∀ j, raw25653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25653step0 = (fun i j => raw25653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25653step0 raw25653; decide +kernel
      have hl : raw25653step0Labels = raw25653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25653 raw25653Labels permutation346 hz
    mixedMoment B raw25653step0 raw25653step0Labels = mixedMoment B raw25653step1 raw25653step1Labels := by
      have hz : ∀ j, raw25653step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25653step1 = (fun i j => raw25653step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25653step1 raw25653step0; decide +kernel
      have hl : raw25653step1Labels = raw25653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25653step0 raw25653step0Labels permutation56 hz
    mixedMoment B raw25653step1 raw25653step1Labels = mixedMoment B raw25653step2 raw25653step2Labels := by
      have ha : raw25653step2 = (fun i j => raw25653step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25653step2 raw25653step1; decide +kernel
      have hl : raw25653step2Labels = raw25653step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25653step1 raw25653step1Labels permutation13 permutation7
    mixedMoment B raw25653step2 raw25653step2Labels = mixedMoment B raw25653step3 raw25653step3Labels := by
      have ha : raw25653step3 = -raw25653step2 := by apply Matrix.ext; change ∀ i j, raw25653step3 i j = -(raw25653step2 i j); unfold raw25653step3 raw25653step2; decide +kernel
      have hl : raw25653step3Labels = raw25653step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25653step3 raw25653step3Labels = mixedMoment B raw25653step4 raw25653step4Labels := by
      have ha : raw25653step4 = raw25653step3 := by apply Matrix.ext; unfold raw25653step4 raw25653step3; decide +kernel
      have hl : raw25653step3Labels = labelEmbedding1 ∘ raw25653step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25653step3 raw25653step3Labels raw25653step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1526 node1526Labels := by rfl

def raw25654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25654Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25654step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25654step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25654step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25654step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25654step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25654 raw25654Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw25654 raw25654Labels = mixedMoment B raw25654step0 raw25654step0Labels := by
      have hz : ∀ j, raw25654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25654step0 = (fun i j => raw25654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25654step0 raw25654; decide +kernel
      have hl : raw25654step0Labels = raw25654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25654 raw25654Labels permutation346 hz
    mixedMoment B raw25654step0 raw25654step0Labels = mixedMoment B raw25654step1 raw25654step1Labels := by
      have ha : raw25654step1 = (fun i j => raw25654step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25654step1 raw25654step0; decide +kernel
      have hl : raw25654step1Labels = raw25654step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25654step0 raw25654step0Labels permutation37 permutation7
    mixedMoment B raw25654step1 raw25654step1Labels = mixedMoment B raw25654step2 raw25654step2Labels := by
      have ha : raw25654step2 = -raw25654step1 := by apply Matrix.ext; change ∀ i j, raw25654step2 i j = -(raw25654step1 i j); unfold raw25654step2 raw25654step1; decide +kernel
      have hl : raw25654step2Labels = raw25654step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25654step2 raw25654step2Labels = mixedMoment B raw25654step3 raw25654step3Labels := by
      have ha : raw25654step3 = raw25654step2 := by apply Matrix.ext; unfold raw25654step3 raw25654step2; decide +kernel
      have hl : raw25654step2Labels = labelEmbedding1 ∘ raw25654step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25654step2 raw25654step2Labels raw25654step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

def raw25655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25655Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25655step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25655step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25655step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25655step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25655step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25655 raw25655Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw25655 raw25655Labels = mixedMoment B raw25655step0 raw25655step0Labels := by
      have hz : ∀ j, raw25655 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25655step0 = (fun i j => raw25655 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25655step0 raw25655; decide +kernel
      have hl : raw25655step0Labels = raw25655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25655 raw25655Labels permutation265 hz
    mixedMoment B raw25655step0 raw25655step0Labels = mixedMoment B raw25655step1 raw25655step1Labels := by
      have ha : raw25655step1 = (fun i j => raw25655step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25655step1 raw25655step0; decide +kernel
      have hl : raw25655step1Labels = raw25655step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25655step0 raw25655step0Labels permutation37 permutation7
    mixedMoment B raw25655step1 raw25655step1Labels = mixedMoment B raw25655step2 raw25655step2Labels := by
      have ha : raw25655step2 = -raw25655step1 := by apply Matrix.ext; change ∀ i j, raw25655step2 i j = -(raw25655step1 i j); unfold raw25655step2 raw25655step1; decide +kernel
      have hl : raw25655step2Labels = raw25655step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25655step2 raw25655step2Labels = mixedMoment B raw25655step3 raw25655step3Labels := by
      have ha : raw25655step3 = raw25655step2 := by apply Matrix.ext; unfold raw25655step3 raw25655step2; decide +kernel
      have hl : raw25655step2Labels = labelEmbedding1 ∘ raw25655step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25655step2 raw25655step2Labels raw25655step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

def raw25656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25656step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25656step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw25656step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25656step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25656step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25656step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25656 raw25656Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw25656 raw25656Labels = mixedMoment B raw25656step0 raw25656step0Labels := by
      have hz : ∀ j, raw25656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25656step0 = (fun i j => raw25656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25656step0 raw25656; decide +kernel
      have hl : raw25656step0Labels = raw25656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25656 raw25656Labels permutation346 hz
    mixedMoment B raw25656step0 raw25656step0Labels = mixedMoment B raw25656step1 raw25656step1Labels := by
      have hz : ∀ j, raw25656step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25656step1 = (fun i j => raw25656step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25656step1 raw25656step0; decide +kernel
      have hl : raw25656step1Labels = raw25656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25656step0 raw25656step0Labels permutation56 hz
    mixedMoment B raw25656step1 raw25656step1Labels = mixedMoment B raw25656step2 raw25656step2Labels := by
      have ha : raw25656step2 = (fun i j => raw25656step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25656step2 raw25656step1; decide +kernel
      have hl : raw25656step2Labels = raw25656step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25656step1 raw25656step1Labels permutation13 permutation7
    mixedMoment B raw25656step2 raw25656step2Labels = mixedMoment B raw25656step3 raw25656step3Labels := by
      have ha : raw25656step3 = -raw25656step2 := by apply Matrix.ext; change ∀ i j, raw25656step3 i j = -(raw25656step2 i j); unfold raw25656step3 raw25656step2; decide +kernel
      have hl : raw25656step3Labels = raw25656step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25656step3 raw25656step3Labels = mixedMoment B raw25656step4 raw25656step4Labels := by
      have ha : raw25656step4 = raw25656step3 := by apply Matrix.ext; unfold raw25656step4 raw25656step3; decide +kernel
      have hl : raw25656step3Labels = labelEmbedding1 ∘ raw25656step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25656step3 raw25656step3Labels raw25656step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

def raw25657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25657Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25657step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25657step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25657step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25657step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25657step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25657step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25657 raw25657Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw25657 raw25657Labels = mixedMoment B raw25657step0 raw25657step0Labels := by
      have hz : ∀ j, raw25657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25657step0 = (fun i j => raw25657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25657step0 raw25657; decide +kernel
      have hl : raw25657step0Labels = raw25657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25657 raw25657Labels permutation346 hz
    mixedMoment B raw25657step0 raw25657step0Labels = mixedMoment B raw25657step1 raw25657step1Labels := by
      have hz : ∀ j, raw25657step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25657step1 = (fun i j => raw25657step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25657step1 raw25657step0; decide +kernel
      have hl : raw25657step1Labels = raw25657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25657step0 raw25657step0Labels permutation56 hz
    mixedMoment B raw25657step1 raw25657step1Labels = mixedMoment B raw25657step2 raw25657step2Labels := by
      have ha : raw25657step2 = (fun i j => raw25657step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25657step2 raw25657step1; decide +kernel
      have hl : raw25657step2Labels = raw25657step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25657step1 raw25657step1Labels permutation13 permutation7
    mixedMoment B raw25657step2 raw25657step2Labels = mixedMoment B raw25657step3 raw25657step3Labels := by
      have ha : raw25657step3 = -raw25657step2 := by apply Matrix.ext; change ∀ i j, raw25657step3 i j = -(raw25657step2 i j); unfold raw25657step3 raw25657step2; decide +kernel
      have hl : raw25657step3Labels = raw25657step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25657step3 raw25657step3Labels = mixedMoment B raw25657step4 raw25657step4Labels := by
      have ha : raw25657step4 = raw25657step3 := by apply Matrix.ext; unfold raw25657step4 raw25657step3; decide +kernel
      have hl : raw25657step3Labels = labelEmbedding1 ∘ raw25657step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25657step3 raw25657step3Labels raw25657step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw25658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25658step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25658step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw25658step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25658step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25658step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25658step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25658 raw25658Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw25658 raw25658Labels = mixedMoment B raw25658step0 raw25658step0Labels := by
      have hz : ∀ j, raw25658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25658step0 = (fun i j => raw25658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25658step0 raw25658; decide +kernel
      have hl : raw25658step0Labels = raw25658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25658 raw25658Labels permutation346 hz
    mixedMoment B raw25658step0 raw25658step0Labels = mixedMoment B raw25658step1 raw25658step1Labels := by
      have hz : ∀ j, raw25658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25658step1 = (fun i j => raw25658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25658step1 raw25658step0; decide +kernel
      have hl : raw25658step1Labels = raw25658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25658step0 raw25658step0Labels permutation56 hz
    mixedMoment B raw25658step1 raw25658step1Labels = mixedMoment B raw25658step2 raw25658step2Labels := by
      have ha : raw25658step2 = (fun i j => raw25658step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25658step2 raw25658step1; decide +kernel
      have hl : raw25658step2Labels = raw25658step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25658step1 raw25658step1Labels permutation13 permutation7
    mixedMoment B raw25658step2 raw25658step2Labels = mixedMoment B raw25658step3 raw25658step3Labels := by
      have ha : raw25658step3 = -raw25658step2 := by apply Matrix.ext; change ∀ i j, raw25658step3 i j = -(raw25658step2 i j); unfold raw25658step3 raw25658step2; decide +kernel
      have hl : raw25658step3Labels = raw25658step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25658step3 raw25658step3Labels = mixedMoment B raw25658step4 raw25658step4Labels := by
      have ha : raw25658step4 = raw25658step3 := by apply Matrix.ext; unfold raw25658step4 raw25658step3; decide +kernel
      have hl : raw25658step3Labels = labelEmbedding1 ∘ raw25658step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25658step3 raw25658step3Labels raw25658step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

def raw25659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25659Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25659step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw25659step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25659step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25659step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25659step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25659 raw25659Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw25659 raw25659Labels = mixedMoment B raw25659step0 raw25659step0Labels := by
      have hz : ∀ j, raw25659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25659step0 = (fun i j => raw25659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25659step0 raw25659; decide +kernel
      have hl : raw25659step0Labels = raw25659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25659 raw25659Labels permutation346 hz
    mixedMoment B raw25659step0 raw25659step0Labels = mixedMoment B raw25659step1 raw25659step1Labels := by
      have ha : raw25659step1 = (fun i j => raw25659step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25659step1 raw25659step0; decide +kernel
      have hl : raw25659step1Labels = raw25659step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25659step0 raw25659step0Labels permutation37 permutation7
    mixedMoment B raw25659step1 raw25659step1Labels = mixedMoment B raw25659step2 raw25659step2Labels := by
      have ha : raw25659step2 = -raw25659step1 := by apply Matrix.ext; change ∀ i j, raw25659step2 i j = -(raw25659step1 i j); unfold raw25659step2 raw25659step1; decide +kernel
      have hl : raw25659step2Labels = raw25659step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25659step2 raw25659step2Labels = mixedMoment B raw25659step3 raw25659step3Labels := by
      have ha : raw25659step3 = raw25659step2 := by apply Matrix.ext; unfold raw25659step3 raw25659step2; decide +kernel
      have hl : raw25659step2Labels = labelEmbedding1 ∘ raw25659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25659step2 raw25659step2Labels raw25659step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

def raw25660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25660Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25660step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw25660step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25660step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25660step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25660step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25660 raw25660Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw25660 raw25660Labels = mixedMoment B raw25660step0 raw25660step0Labels := by
      have hz : ∀ j, raw25660 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25660step0 = (fun i j => raw25660 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25660step0 raw25660; decide +kernel
      have hl : raw25660step0Labels = raw25660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25660 raw25660Labels permutation265 hz
    mixedMoment B raw25660step0 raw25660step0Labels = mixedMoment B raw25660step1 raw25660step1Labels := by
      have ha : raw25660step1 = (fun i j => raw25660step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25660step1 raw25660step0; decide +kernel
      have hl : raw25660step1Labels = raw25660step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25660step0 raw25660step0Labels permutation37 permutation7
    mixedMoment B raw25660step1 raw25660step1Labels = mixedMoment B raw25660step2 raw25660step2Labels := by
      have ha : raw25660step2 = -raw25660step1 := by apply Matrix.ext; change ∀ i j, raw25660step2 i j = -(raw25660step1 i j); unfold raw25660step2 raw25660step1; decide +kernel
      have hl : raw25660step2Labels = raw25660step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25660step2 raw25660step2Labels = mixedMoment B raw25660step3 raw25660step3Labels := by
      have ha : raw25660step3 = raw25660step2 := by apply Matrix.ext; unfold raw25660step3 raw25660step2; decide +kernel
      have hl : raw25660step2Labels = labelEmbedding1 ∘ raw25660step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25660step2 raw25660step2Labels raw25660step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

def raw25661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25661Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25661step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25661step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw25661step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw25661step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25661step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw25661step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25661 raw25661Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw25661 raw25661Labels = mixedMoment B raw25661step0 raw25661step0Labels := by
      have hz : ∀ j, raw25661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25661step0 = (fun i j => raw25661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25661step0 raw25661; decide +kernel
      have hl : raw25661step0Labels = raw25661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25661 raw25661Labels permutation346 hz
    mixedMoment B raw25661step0 raw25661step0Labels = mixedMoment B raw25661step1 raw25661step1Labels := by
      have hz : ∀ j, raw25661step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25661step1 = (fun i j => raw25661step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25661step1 raw25661step0; decide +kernel
      have hl : raw25661step1Labels = raw25661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25661step0 raw25661step0Labels permutation56 hz
    mixedMoment B raw25661step1 raw25661step1Labels = mixedMoment B raw25661step2 raw25661step2Labels := by
      have ha : raw25661step2 = (fun i j => raw25661step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25661step2 raw25661step1; decide +kernel
      have hl : raw25661step2Labels = raw25661step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25661step1 raw25661step1Labels permutation13 permutation7
    mixedMoment B raw25661step2 raw25661step2Labels = mixedMoment B raw25661step3 raw25661step3Labels := by
      have ha : raw25661step3 = -raw25661step2 := by apply Matrix.ext; change ∀ i j, raw25661step3 i j = -(raw25661step2 i j); unfold raw25661step3 raw25661step2; decide +kernel
      have hl : raw25661step3Labels = raw25661step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25661step3 raw25661step3Labels = mixedMoment B raw25661step4 raw25661step4Labels := by
      have ha : raw25661step4 = raw25661step3 := by apply Matrix.ext; unfold raw25661step4 raw25661step3; decide +kernel
      have hl : raw25661step3Labels = labelEmbedding1 ∘ raw25661step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25661step3 raw25661step3Labels raw25661step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

def raw25662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25662Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25662step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25662step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw25662step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw25662step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25662step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw25662step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25662 raw25662Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw25662 raw25662Labels = mixedMoment B raw25662step0 raw25662step0Labels := by
      have hz : ∀ j, raw25662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25662step0 = (fun i j => raw25662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25662step0 raw25662; decide +kernel
      have hl : raw25662step0Labels = raw25662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25662 raw25662Labels permutation346 hz
    mixedMoment B raw25662step0 raw25662step0Labels = mixedMoment B raw25662step1 raw25662step1Labels := by
      have hz : ∀ j, raw25662step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25662step1 = (fun i j => raw25662step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25662step1 raw25662step0; decide +kernel
      have hl : raw25662step1Labels = raw25662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25662step0 raw25662step0Labels permutation56 hz
    mixedMoment B raw25662step1 raw25662step1Labels = mixedMoment B raw25662step2 raw25662step2Labels := by
      have ha : raw25662step2 = (fun i j => raw25662step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25662step2 raw25662step1; decide +kernel
      have hl : raw25662step2Labels = raw25662step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25662step1 raw25662step1Labels permutation13 permutation7
    mixedMoment B raw25662step2 raw25662step2Labels = mixedMoment B raw25662step3 raw25662step3Labels := by
      have ha : raw25662step3 = -raw25662step2 := by apply Matrix.ext; change ∀ i j, raw25662step3 i j = -(raw25662step2 i j); unfold raw25662step3 raw25662step2; decide +kernel
      have hl : raw25662step3Labels = raw25662step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25662step3 raw25662step3Labels = mixedMoment B raw25662step4 raw25662step4Labels := by
      have ha : raw25662step4 = raw25662step3 := by apply Matrix.ext; unfold raw25662step4 raw25662step3; decide +kernel
      have hl : raw25662step3Labels = labelEmbedding1 ∘ raw25662step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25662step3 raw25662step3Labels raw25662step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw25663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25663step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25663 raw25663Labels = mixedMoment B node4126 node4126Labels := by
  calc
    mixedMoment B raw25663 raw25663Labels = mixedMoment B raw25663step0 raw25663step0Labels := by
      have hz : ∀ j, raw25663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25663step0 = (fun i j => raw25663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25663step0 raw25663; decide +kernel
      have hl : raw25663step0Labels = raw25663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25663 raw25663Labels permutation346 hz
    mixedMoment B raw25663step0 raw25663step0Labels = mixedMoment B raw25663step1 raw25663step1Labels := by
      have ha : raw25663step1 = (fun i j => raw25663step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25663step1 raw25663step0; decide +kernel
      have hl : raw25663step1Labels = raw25663step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25663step0 raw25663step0Labels permutation34 permutation3
    mixedMoment B raw25663step1 raw25663step1Labels = mixedMoment B raw25663step2 raw25663step2Labels := by
      have ha : raw25663step2 = raw25663step1 := by apply Matrix.ext; unfold raw25663step2 raw25663step1; decide +kernel
      have hl : raw25663step1Labels = labelEmbedding6 ∘ raw25663step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25663step1 raw25663step1Labels raw25663step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4126 node4126Labels := by rfl

def raw25664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25664step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25664 raw25664Labels = mixedMoment B node4307 node4307Labels := by
  calc
    mixedMoment B raw25664 raw25664Labels = mixedMoment B raw25664step0 raw25664step0Labels := by
      have ha : raw25664step0 = (fun i j => raw25664 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25664step0 raw25664; decide +kernel
      have hl : raw25664step0Labels = raw25664Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25664 raw25664Labels permutation178 permutation3
    mixedMoment B raw25664step0 raw25664step0Labels = mixedMoment B raw25664step1 raw25664step1Labels := by
      have ha : raw25664step1 = raw25664step0 := by apply Matrix.ext; unfold raw25664step1 raw25664step0; decide +kernel
      have hl : raw25664step0Labels = labelEmbedding6 ∘ raw25664step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25664step0 raw25664step0Labels raw25664step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4307 node4307Labels := by rfl

def raw25665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw25665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw25665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw25665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25665step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25665 raw25665Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw25665 raw25665Labels = mixedMoment B raw25665step0 raw25665step0Labels := by
      have hz : ∀ j, raw25665 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25665step0 = (fun i j => raw25665 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25665step0 raw25665; decide +kernel
      have hl : raw25665step0Labels = raw25665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25665 raw25665Labels permutation520 hz
    mixedMoment B raw25665step0 raw25665step0Labels = mixedMoment B raw25665step1 raw25665step1Labels := by
      have hz : ∀ j, raw25665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25665step1 = (fun i j => raw25665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25665step1 raw25665step0; decide +kernel
      have hl : raw25665step1Labels = raw25665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25665step0 raw25665step0Labels permutation80 hz
    mixedMoment B raw25665step1 raw25665step1Labels = mixedMoment B raw25665step2 raw25665step2Labels := by
      have ha : raw25665step2 = (fun i j => raw25665step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25665step2 raw25665step1; decide +kernel
      have hl : raw25665step2Labels = raw25665step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25665step1 raw25665step1Labels permutation8 permutation3
    mixedMoment B raw25665step2 raw25665step2Labels = mixedMoment B raw25665step3 raw25665step3Labels := by
      have ha : raw25665step3 = raw25665step2 := by apply Matrix.ext; unfold raw25665step3 raw25665step2; decide +kernel
      have hl : raw25665step2Labels = labelEmbedding6 ∘ raw25665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25665step2 raw25665step2Labels raw25665step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw25666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25666step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25666 raw25666Labels = mixedMoment B node4126 node4126Labels := by
  calc
    mixedMoment B raw25666 raw25666Labels = mixedMoment B raw25666step0 raw25666step0Labels := by
      have hz : ∀ j, raw25666 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25666step0 = (fun i j => raw25666 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25666step0 raw25666; decide +kernel
      have hl : raw25666step0Labels = raw25666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25666 raw25666Labels permutation265 hz
    mixedMoment B raw25666step0 raw25666step0Labels = mixedMoment B raw25666step1 raw25666step1Labels := by
      have ha : raw25666step1 = (fun i j => raw25666step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25666step1 raw25666step0; decide +kernel
      have hl : raw25666step1Labels = raw25666step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25666step0 raw25666step0Labels permutation34 permutation3
    mixedMoment B raw25666step1 raw25666step1Labels = mixedMoment B raw25666step2 raw25666step2Labels := by
      have ha : raw25666step2 = raw25666step1 := by apply Matrix.ext; unfold raw25666step2 raw25666step1; decide +kernel
      have hl : raw25666step1Labels = labelEmbedding6 ∘ raw25666step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25666step1 raw25666step1Labels raw25666step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4126 node4126Labels := by rfl

def raw25667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25667step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25667 raw25667Labels = mixedMoment B node4307 node4307Labels := by
  calc
    mixedMoment B raw25667 raw25667Labels = mixedMoment B raw25667step0 raw25667step0Labels := by
      have ha : raw25667step0 = (fun i j => raw25667 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25667step0 raw25667; decide +kernel
      have hl : raw25667step0Labels = raw25667Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25667 raw25667Labels permutation154 permutation3
    mixedMoment B raw25667step0 raw25667step0Labels = mixedMoment B raw25667step1 raw25667step1Labels := by
      have ha : raw25667step1 = raw25667step0 := by apply Matrix.ext; unfold raw25667step1 raw25667step0; decide +kernel
      have hl : raw25667step0Labels = labelEmbedding6 ∘ raw25667step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25667step0 raw25667step0Labels raw25667step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4307 node4307Labels := by rfl

def raw25668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw25668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw25668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw25668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25668step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25668step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25668 raw25668Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw25668 raw25668Labels = mixedMoment B raw25668step0 raw25668step0Labels := by
      have hz : ∀ j, raw25668 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25668step0 = (fun i j => raw25668 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25668step0 raw25668; decide +kernel
      have hl : raw25668step0Labels = raw25668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25668 raw25668Labels permutation520 hz
    mixedMoment B raw25668step0 raw25668step0Labels = mixedMoment B raw25668step1 raw25668step1Labels := by
      have hz : ∀ j, raw25668step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25668step1 = (fun i j => raw25668step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25668step1 raw25668step0; decide +kernel
      have hl : raw25668step1Labels = raw25668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25668step0 raw25668step0Labels permutation56 hz
    mixedMoment B raw25668step1 raw25668step1Labels = mixedMoment B raw25668step2 raw25668step2Labels := by
      have ha : raw25668step2 = (fun i j => raw25668step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25668step2 raw25668step1; decide +kernel
      have hl : raw25668step2Labels = raw25668step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25668step1 raw25668step1Labels permutation8 permutation3
    mixedMoment B raw25668step2 raw25668step2Labels = mixedMoment B raw25668step3 raw25668step3Labels := by
      have ha : raw25668step3 = raw25668step2 := by apply Matrix.ext; unfold raw25668step3 raw25668step2; decide +kernel
      have hl : raw25668step2Labels = labelEmbedding6 ∘ raw25668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25668step2 raw25668step2Labels raw25668step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw25669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw25669step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25669step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw25669step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25669 raw25669Labels = mixedMoment B node4129 node4129Labels := by
  calc
    mixedMoment B raw25669 raw25669Labels = mixedMoment B raw25669step0 raw25669step0Labels := by
      have hz : ∀ j, raw25669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25669step0 = (fun i j => raw25669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25669step0 raw25669; decide +kernel
      have hl : raw25669step0Labels = raw25669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25669 raw25669Labels permutation346 hz
    mixedMoment B raw25669step0 raw25669step0Labels = mixedMoment B raw25669step1 raw25669step1Labels := by
      have hz : ∀ j, raw25669step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25669step1 = (fun i j => raw25669step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25669step1 raw25669step0; decide +kernel
      have hl : raw25669step1Labels = raw25669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25669step0 raw25669step0Labels permutation56 hz
    mixedMoment B raw25669step1 raw25669step1Labels = mixedMoment B raw25669step2 raw25669step2Labels := by
      have ha : raw25669step2 = (fun i j => raw25669step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25669step2 raw25669step1; decide +kernel
      have hl : raw25669step2Labels = raw25669step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25669step1 raw25669step1Labels permutation11 permutation3
    mixedMoment B raw25669step2 raw25669step2Labels = mixedMoment B raw25669step3 raw25669step3Labels := by
      have ha : raw25669step3 = raw25669step2 := by apply Matrix.ext; unfold raw25669step3 raw25669step2; decide +kernel
      have hl : raw25669step2Labels = labelEmbedding6 ∘ raw25669step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25669step2 raw25669step2Labels raw25669step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4129 node4129Labels := by rfl

def raw25670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw25670step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw25670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25670 raw25670Labels = mixedMoment B node4310 node4310Labels := by
  calc
    mixedMoment B raw25670 raw25670Labels = mixedMoment B raw25670step0 raw25670step0Labels := by
      have hz : ∀ j, raw25670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25670step0 = (fun i j => raw25670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25670step0 raw25670; decide +kernel
      have hl : raw25670step0Labels = raw25670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25670 raw25670Labels permutation346 hz
    mixedMoment B raw25670step0 raw25670step0Labels = mixedMoment B raw25670step1 raw25670step1Labels := by
      have ha : raw25670step1 = (fun i j => raw25670step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25670step1 raw25670step0; decide +kernel
      have hl : raw25670step1Labels = raw25670step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25670step0 raw25670step0Labels permutation35 permutation3
    mixedMoment B raw25670step1 raw25670step1Labels = mixedMoment B raw25670step2 raw25670step2Labels := by
      have ha : raw25670step2 = raw25670step1 := by apply Matrix.ext; unfold raw25670step2 raw25670step1; decide +kernel
      have hl : raw25670step1Labels = labelEmbedding6 ∘ raw25670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25670step1 raw25670step1Labels raw25670step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4310 node4310Labels := by rfl

def raw25671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw25671step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw25671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25671 raw25671Labels = mixedMoment B node4310 node4310Labels := by
  calc
    mixedMoment B raw25671 raw25671Labels = mixedMoment B raw25671step0 raw25671step0Labels := by
      have hz : ∀ j, raw25671 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25671step0 = (fun i j => raw25671 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25671step0 raw25671; decide +kernel
      have hl : raw25671step0Labels = raw25671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25671 raw25671Labels permutation265 hz
    mixedMoment B raw25671step0 raw25671step0Labels = mixedMoment B raw25671step1 raw25671step1Labels := by
      have ha : raw25671step1 = (fun i j => raw25671step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25671step1 raw25671step0; decide +kernel
      have hl : raw25671step1Labels = raw25671step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25671step0 raw25671step0Labels permutation35 permutation3
    mixedMoment B raw25671step1 raw25671step1Labels = mixedMoment B raw25671step2 raw25671step2Labels := by
      have ha : raw25671step2 = raw25671step1 := by apply Matrix.ext; unfold raw25671step2 raw25671step1; decide +kernel
      have hl : raw25671step1Labels = labelEmbedding6 ∘ raw25671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25671step1 raw25671step1Labels raw25671step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4310 node4310Labels := by rfl

def raw25672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![2, 0, -2]]
def raw25672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw25672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw25672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25672step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw25672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25672step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25672step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25672step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25672step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25672 raw25672Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw25672 raw25672Labels = mixedMoment B raw25672step0 raw25672step0Labels := by
      have hz : ∀ j, raw25672 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25672step0 = (fun i j => raw25672 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25672step0 raw25672; decide +kernel
      have hl : raw25672step0Labels = raw25672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25672 raw25672Labels permutation520 hz
    mixedMoment B raw25672step0 raw25672step0Labels = mixedMoment B raw25672step1 raw25672step1Labels := by
      have hz : ∀ j, raw25672step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25672step1 = (fun i j => raw25672step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25672step1 raw25672step0; decide +kernel
      have hl : raw25672step1Labels = raw25672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25672step0 raw25672step0Labels permutation80 hz
    mixedMoment B raw25672step1 raw25672step1Labels = mixedMoment B raw25672step2 raw25672step2Labels := by
      have hz : ∀ j, raw25672step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25672step2 = (fun i j => raw25672step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25672step2 raw25672step1; decide +kernel
      have hl : raw25672step2Labels = raw25672step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25672step1 raw25672step1Labels permutation14 hz
    mixedMoment B raw25672step2 raw25672step2Labels = mixedMoment B raw25672step3 raw25672step3Labels := by
      have ha : raw25672step3 = (fun i j => raw25672step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25672step3 raw25672step2; decide +kernel
      have hl : raw25672step3Labels = raw25672step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25672step2 raw25672step2Labels permutation3 permutation3
    mixedMoment B raw25672step3 raw25672step3Labels = mixedMoment B raw25672step4 raw25672step4Labels := by
      have ha : raw25672step4 = raw25672step3 := by apply Matrix.ext; unfold raw25672step4 raw25672step3; decide +kernel
      have hl : raw25672step3Labels = labelEmbedding6 ∘ raw25672step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25672step3 raw25672step3Labels raw25672step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw25673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw25673step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw25673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25673 raw25673Labels = mixedMoment B node4132 node4132Labels := by
  calc
    mixedMoment B raw25673 raw25673Labels = mixedMoment B raw25673step0 raw25673step0Labels := by
      have hz : ∀ j, raw25673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25673step0 = (fun i j => raw25673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25673step0 raw25673; decide +kernel
      have hl : raw25673step0Labels = raw25673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25673 raw25673Labels permutation346 hz
    mixedMoment B raw25673step0 raw25673step0Labels = mixedMoment B raw25673step1 raw25673step1Labels := by
      have hz : ∀ j, raw25673step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25673step1 = (fun i j => raw25673step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25673step1 raw25673step0; decide +kernel
      have hl : raw25673step1Labels = raw25673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25673step0 raw25673step0Labels permutation56 hz
    mixedMoment B raw25673step1 raw25673step1Labels = mixedMoment B raw25673step2 raw25673step2Labels := by
      have ha : raw25673step2 = (fun i j => raw25673step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25673step2 raw25673step1; decide +kernel
      have hl : raw25673step2Labels = raw25673step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25673step1 raw25673step1Labels permutation9 permutation3
    mixedMoment B raw25673step2 raw25673step2Labels = mixedMoment B raw25673step3 raw25673step3Labels := by
      have ha : raw25673step3 = raw25673step2 := by apply Matrix.ext; unfold raw25673step3 raw25673step2; decide +kernel
      have hl : raw25673step2Labels = labelEmbedding6 ∘ raw25673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25673step2 raw25673step2Labels raw25673step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4132 node4132Labels := by rfl

def raw25674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw25674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw25674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25674 raw25674Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw25674 raw25674Labels = mixedMoment B raw25674step0 raw25674step0Labels := by
      have hz : ∀ j, raw25674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25674step0 = (fun i j => raw25674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25674step0 raw25674; decide +kernel
      have hl : raw25674step0Labels = raw25674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25674 raw25674Labels permutation346 hz
    mixedMoment B raw25674step0 raw25674step0Labels = mixedMoment B raw25674step1 raw25674step1Labels := by
      have ha : raw25674step1 = (fun i j => raw25674step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25674step1 raw25674step0; decide +kernel
      have hl : raw25674step1Labels = raw25674step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25674step0 raw25674step0Labels permutation33 permutation3
    mixedMoment B raw25674step1 raw25674step1Labels = mixedMoment B raw25674step2 raw25674step2Labels := by
      have ha : raw25674step2 = raw25674step1 := by apply Matrix.ext; unfold raw25674step2 raw25674step1; decide +kernel
      have hl : raw25674step1Labels = labelEmbedding6 ∘ raw25674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25674step1 raw25674step1Labels raw25674step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

def raw25675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw25675step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw25675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25675 raw25675Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw25675 raw25675Labels = mixedMoment B raw25675step0 raw25675step0Labels := by
      have hz : ∀ j, raw25675 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25675step0 = (fun i j => raw25675 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25675step0 raw25675; decide +kernel
      have hl : raw25675step0Labels = raw25675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25675 raw25675Labels permutation265 hz
    mixedMoment B raw25675step0 raw25675step0Labels = mixedMoment B raw25675step1 raw25675step1Labels := by
      have ha : raw25675step1 = (fun i j => raw25675step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25675step1 raw25675step0; decide +kernel
      have hl : raw25675step1Labels = raw25675step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25675step0 raw25675step0Labels permutation33 permutation3
    mixedMoment B raw25675step1 raw25675step1Labels = mixedMoment B raw25675step2 raw25675step2Labels := by
      have ha : raw25675step2 = raw25675step1 := by apply Matrix.ext; unfold raw25675step2 raw25675step1; decide +kernel
      have hl : raw25675step1Labels = labelEmbedding6 ∘ raw25675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25675step1 raw25675step1Labels raw25675step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

def raw25676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25676step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25676step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25676 raw25676Labels = mixedMoment B node4128 node4128Labels := by
  calc
    mixedMoment B raw25676 raw25676Labels = mixedMoment B raw25676step0 raw25676step0Labels := by
      have hz : ∀ j, raw25676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25676step0 = (fun i j => raw25676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25676step0 raw25676; decide +kernel
      have hl : raw25676step0Labels = raw25676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25676 raw25676Labels permutation346 hz
    mixedMoment B raw25676step0 raw25676step0Labels = mixedMoment B raw25676step1 raw25676step1Labels := by
      have hz : ∀ j, raw25676step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25676step1 = (fun i j => raw25676step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25676step1 raw25676step0; decide +kernel
      have hl : raw25676step1Labels = raw25676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25676step0 raw25676step0Labels permutation56 hz
    mixedMoment B raw25676step1 raw25676step1Labels = mixedMoment B raw25676step2 raw25676step2Labels := by
      have ha : raw25676step2 = (fun i j => raw25676step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25676step2 raw25676step1; decide +kernel
      have hl : raw25676step2Labels = raw25676step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25676step1 raw25676step1Labels permutation10 permutation3
    mixedMoment B raw25676step2 raw25676step2Labels = mixedMoment B raw25676step3 raw25676step3Labels := by
      have ha : raw25676step3 = raw25676step2 := by apply Matrix.ext; unfold raw25676step3 raw25676step2; decide +kernel
      have hl : raw25676step2Labels = labelEmbedding6 ∘ raw25676step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25676step2 raw25676step2Labels raw25676step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4128 node4128Labels := by rfl

def raw25677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25677 raw25677Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw25677 raw25677Labels = mixedMoment B raw25677step0 raw25677step0Labels := by
      have hz : ∀ j, raw25677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25677step0 = (fun i j => raw25677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25677step0 raw25677; decide +kernel
      have hl : raw25677step0Labels = raw25677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25677 raw25677Labels permutation346 hz
    mixedMoment B raw25677step0 raw25677step0Labels = mixedMoment B raw25677step1 raw25677step1Labels := by
      have ha : raw25677step1 = (fun i j => raw25677step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25677step1 raw25677step0; decide +kernel
      have hl : raw25677step1Labels = raw25677step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25677step0 raw25677step0Labels permutation34 permutation3
    mixedMoment B raw25677step1 raw25677step1Labels = mixedMoment B raw25677step2 raw25677step2Labels := by
      have ha : raw25677step2 = raw25677step1 := by apply Matrix.ext; unfold raw25677step2 raw25677step1; decide +kernel
      have hl : raw25677step1Labels = labelEmbedding6 ∘ raw25677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25677step1 raw25677step1Labels raw25677step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw25678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25678step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25678 raw25678Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw25678 raw25678Labels = mixedMoment B raw25678step0 raw25678step0Labels := by
      have hz : ∀ j, raw25678 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25678step0 = (fun i j => raw25678 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25678step0 raw25678; decide +kernel
      have hl : raw25678step0Labels = raw25678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25678 raw25678Labels permutation265 hz
    mixedMoment B raw25678step0 raw25678step0Labels = mixedMoment B raw25678step1 raw25678step1Labels := by
      have ha : raw25678step1 = (fun i j => raw25678step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25678step1 raw25678step0; decide +kernel
      have hl : raw25678step1Labels = raw25678step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25678step0 raw25678step0Labels permutation34 permutation3
    mixedMoment B raw25678step1 raw25678step1Labels = mixedMoment B raw25678step2 raw25678step2Labels := by
      have ha : raw25678step2 = raw25678step1 := by apply Matrix.ext; unfold raw25678step2 raw25678step1; decide +kernel
      have hl : raw25678step1Labels = labelEmbedding6 ∘ raw25678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25678step1 raw25678step1Labels raw25678step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw25679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, -1, -2]]
def raw25679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw25679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw25679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25679step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw25679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25679step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw25679step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25679step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw25679step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25679 raw25679Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw25679 raw25679Labels = mixedMoment B raw25679step0 raw25679step0Labels := by
      have hz : ∀ j, raw25679 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25679step0 = (fun i j => raw25679 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25679step0 raw25679; decide +kernel
      have hl : raw25679step0Labels = raw25679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25679 raw25679Labels permutation520 hz
    mixedMoment B raw25679step0 raw25679step0Labels = mixedMoment B raw25679step1 raw25679step1Labels := by
      have hz : ∀ j, raw25679step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25679step1 = (fun i j => raw25679step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25679step1 raw25679step0; decide +kernel
      have hl : raw25679step1Labels = raw25679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25679step0 raw25679step0Labels permutation80 hz
    mixedMoment B raw25679step1 raw25679step1Labels = mixedMoment B raw25679step2 raw25679step2Labels := by
      have hz : ∀ j, raw25679step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25679step2 = (fun i j => raw25679step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25679step2 raw25679step1; decide +kernel
      have hl : raw25679step2Labels = raw25679step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25679step1 raw25679step1Labels permutation14 hz
    mixedMoment B raw25679step2 raw25679step2Labels = mixedMoment B raw25679step3 raw25679step3Labels := by
      have ha : raw25679step3 = (fun i j => raw25679step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25679step3 raw25679step2; decide +kernel
      have hl : raw25679step3Labels = raw25679step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25679step2 raw25679step2Labels permutation2 permutation3
    mixedMoment B raw25679step3 raw25679step3Labels = mixedMoment B raw25679step4 raw25679step4Labels := by
      have ha : raw25679step4 = raw25679step3 := by apply Matrix.ext; unfold raw25679step4 raw25679step3; decide +kernel
      have hl : raw25679step3Labels = labelEmbedding6 ∘ raw25679step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25679step3 raw25679step3Labels raw25679step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw25680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25680 raw25680Labels = mixedMoment B node557 node557Labels := by
  calc
    mixedMoment B raw25680 raw25680Labels = mixedMoment B raw25680step0 raw25680step0Labels := by
      have hz : ∀ j, raw25680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25680step0 = (fun i j => raw25680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25680step0 raw25680; decide +kernel
      have hl : raw25680step0Labels = raw25680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25680 raw25680Labels permutation346 hz
    mixedMoment B raw25680step0 raw25680step0Labels = mixedMoment B raw25680step1 raw25680step1Labels := by
      have ha : raw25680step1 = (fun i j => raw25680step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25680step1 raw25680step0; decide +kernel
      have hl : raw25680step1Labels = raw25680step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25680step0 raw25680step0Labels permutation34 permutation3
    _ = mixedMoment B node557 node557Labels := by rfl

def raw25681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25681 raw25681Labels = mixedMoment B node885 node885Labels := by
  calc
    mixedMoment B raw25681 raw25681Labels = mixedMoment B raw25681step0 raw25681step0Labels := by
      have ha : raw25681step0 = (fun i j => raw25681 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25681step0 raw25681; decide +kernel
      have hl : raw25681step0Labels = raw25681Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25681 raw25681Labels permutation178 permutation3
    _ = mixedMoment B node885 node885Labels := by rfl

def raw25682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw25682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw25682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw25682step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25682 raw25682Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw25682 raw25682Labels = mixedMoment B raw25682step0 raw25682step0Labels := by
      have hz : ∀ j, raw25682 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25682step0 = (fun i j => raw25682 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25682step0 raw25682; decide +kernel
      have hl : raw25682step0Labels = raw25682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25682 raw25682Labels permutation520 hz
    mixedMoment B raw25682step0 raw25682step0Labels = mixedMoment B raw25682step1 raw25682step1Labels := by
      have hz : ∀ j, raw25682step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25682step1 = (fun i j => raw25682step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25682step1 raw25682step0; decide +kernel
      have hl : raw25682step1Labels = raw25682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25682step0 raw25682step0Labels permutation80 hz
    mixedMoment B raw25682step1 raw25682step1Labels = mixedMoment B raw25682step2 raw25682step2Labels := by
      have ha : raw25682step2 = (fun i j => raw25682step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25682step2 raw25682step1; decide +kernel
      have hl : raw25682step2Labels = raw25682step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25682step1 raw25682step1Labels permutation8 permutation3
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw25683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25683step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25683 raw25683Labels = mixedMoment B node557 node557Labels := by
  calc
    mixedMoment B raw25683 raw25683Labels = mixedMoment B raw25683step0 raw25683step0Labels := by
      have hz : ∀ j, raw25683 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25683step0 = (fun i j => raw25683 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25683step0 raw25683; decide +kernel
      have hl : raw25683step0Labels = raw25683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25683 raw25683Labels permutation265 hz
    mixedMoment B raw25683step0 raw25683step0Labels = mixedMoment B raw25683step1 raw25683step1Labels := by
      have ha : raw25683step1 = (fun i j => raw25683step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25683step1 raw25683step0; decide +kernel
      have hl : raw25683step1Labels = raw25683step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25683step0 raw25683step0Labels permutation34 permutation3
    _ = mixedMoment B node557 node557Labels := by rfl

def raw25684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25684 raw25684Labels = mixedMoment B node885 node885Labels := by
  calc
    mixedMoment B raw25684 raw25684Labels = mixedMoment B raw25684step0 raw25684step0Labels := by
      have ha : raw25684step0 = (fun i j => raw25684 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25684step0 raw25684; decide +kernel
      have hl : raw25684step0Labels = raw25684Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25684 raw25684Labels permutation154 permutation3
    _ = mixedMoment B node885 node885Labels := by rfl

def raw25685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw25685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw25685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw25685step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25685 raw25685Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw25685 raw25685Labels = mixedMoment B raw25685step0 raw25685step0Labels := by
      have hz : ∀ j, raw25685 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25685step0 = (fun i j => raw25685 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25685step0 raw25685; decide +kernel
      have hl : raw25685step0Labels = raw25685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25685 raw25685Labels permutation520 hz
    mixedMoment B raw25685step0 raw25685step0Labels = mixedMoment B raw25685step1 raw25685step1Labels := by
      have hz : ∀ j, raw25685step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25685step1 = (fun i j => raw25685step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25685step1 raw25685step0; decide +kernel
      have hl : raw25685step1Labels = raw25685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25685step0 raw25685step0Labels permutation56 hz
    mixedMoment B raw25685step1 raw25685step1Labels = mixedMoment B raw25685step2 raw25685step2Labels := by
      have ha : raw25685step2 = (fun i j => raw25685step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25685step2 raw25685step1; decide +kernel
      have hl : raw25685step2Labels = raw25685step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25685step1 raw25685step1Labels permutation8 permutation3
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw25686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25686step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw25686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25686 raw25686Labels = mixedMoment B node560 node560Labels := by
  calc
    mixedMoment B raw25686 raw25686Labels = mixedMoment B raw25686step0 raw25686step0Labels := by
      have hz : ∀ j, raw25686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25686step0 = (fun i j => raw25686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25686step0 raw25686; decide +kernel
      have hl : raw25686step0Labels = raw25686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25686 raw25686Labels permutation346 hz
    mixedMoment B raw25686step0 raw25686step0Labels = mixedMoment B raw25686step1 raw25686step1Labels := by
      have hz : ∀ j, raw25686step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25686step1 = (fun i j => raw25686step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25686step1 raw25686step0; decide +kernel
      have hl : raw25686step1Labels = raw25686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25686step0 raw25686step0Labels permutation56 hz
    mixedMoment B raw25686step1 raw25686step1Labels = mixedMoment B raw25686step2 raw25686step2Labels := by
      have ha : raw25686step2 = (fun i j => raw25686step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25686step2 raw25686step1; decide +kernel
      have hl : raw25686step2Labels = raw25686step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25686step1 raw25686step1Labels permutation11 permutation3
    _ = mixedMoment B node560 node560Labels := by rfl

def raw25687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw25687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25687 raw25687Labels = mixedMoment B node888 node888Labels := by
  calc
    mixedMoment B raw25687 raw25687Labels = mixedMoment B raw25687step0 raw25687step0Labels := by
      have hz : ∀ j, raw25687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25687step0 = (fun i j => raw25687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25687step0 raw25687; decide +kernel
      have hl : raw25687step0Labels = raw25687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25687 raw25687Labels permutation346 hz
    mixedMoment B raw25687step0 raw25687step0Labels = mixedMoment B raw25687step1 raw25687step1Labels := by
      have ha : raw25687step1 = (fun i j => raw25687step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25687step1 raw25687step0; decide +kernel
      have hl : raw25687step1Labels = raw25687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25687step0 raw25687step0Labels permutation35 permutation3
    _ = mixedMoment B node888 node888Labels := by rfl

def raw25688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw25688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25688 raw25688Labels = mixedMoment B node888 node888Labels := by
  calc
    mixedMoment B raw25688 raw25688Labels = mixedMoment B raw25688step0 raw25688step0Labels := by
      have hz : ∀ j, raw25688 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25688step0 = (fun i j => raw25688 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25688step0 raw25688; decide +kernel
      have hl : raw25688step0Labels = raw25688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25688 raw25688Labels permutation265 hz
    mixedMoment B raw25688step0 raw25688step0Labels = mixedMoment B raw25688step1 raw25688step1Labels := by
      have ha : raw25688step1 = (fun i j => raw25688step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25688step1 raw25688step0; decide +kernel
      have hl : raw25688step1Labels = raw25688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25688step0 raw25688step0Labels permutation35 permutation3
    _ = mixedMoment B node888 node888Labels := by rfl

def raw25689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![2, 0, -2]]
def raw25689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw25689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw25689step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25689step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw25689step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25689step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25689step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25689 raw25689Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw25689 raw25689Labels = mixedMoment B raw25689step0 raw25689step0Labels := by
      have hz : ∀ j, raw25689 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25689step0 = (fun i j => raw25689 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25689step0 raw25689; decide +kernel
      have hl : raw25689step0Labels = raw25689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25689 raw25689Labels permutation520 hz
    mixedMoment B raw25689step0 raw25689step0Labels = mixedMoment B raw25689step1 raw25689step1Labels := by
      have hz : ∀ j, raw25689step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25689step1 = (fun i j => raw25689step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25689step1 raw25689step0; decide +kernel
      have hl : raw25689step1Labels = raw25689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25689step0 raw25689step0Labels permutation80 hz
    mixedMoment B raw25689step1 raw25689step1Labels = mixedMoment B raw25689step2 raw25689step2Labels := by
      have hz : ∀ j, raw25689step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25689step2 = (fun i j => raw25689step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25689step2 raw25689step1; decide +kernel
      have hl : raw25689step2Labels = raw25689step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25689step1 raw25689step1Labels permutation14 hz
    mixedMoment B raw25689step2 raw25689step2Labels = mixedMoment B raw25689step3 raw25689step3Labels := by
      have ha : raw25689step3 = (fun i j => raw25689step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25689step3 raw25689step2; decide +kernel
      have hl : raw25689step3Labels = raw25689step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25689step2 raw25689step2Labels permutation3 permutation3
    _ = mixedMoment B node1094 node1094Labels := by rfl

def raw25690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25690step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw25690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25690 raw25690Labels = mixedMoment B node562 node562Labels := by
  calc
    mixedMoment B raw25690 raw25690Labels = mixedMoment B raw25690step0 raw25690step0Labels := by
      have hz : ∀ j, raw25690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25690step0 = (fun i j => raw25690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25690step0 raw25690; decide +kernel
      have hl : raw25690step0Labels = raw25690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25690 raw25690Labels permutation346 hz
    mixedMoment B raw25690step0 raw25690step0Labels = mixedMoment B raw25690step1 raw25690step1Labels := by
      have hz : ∀ j, raw25690step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25690step1 = (fun i j => raw25690step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25690step1 raw25690step0; decide +kernel
      have hl : raw25690step1Labels = raw25690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25690step0 raw25690step0Labels permutation56 hz
    mixedMoment B raw25690step1 raw25690step1Labels = mixedMoment B raw25690step2 raw25690step2Labels := by
      have ha : raw25690step2 = (fun i j => raw25690step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25690step2 raw25690step1; decide +kernel
      have hl : raw25690step2Labels = raw25690step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25690step1 raw25690step1Labels permutation9 permutation3
    _ = mixedMoment B node562 node562Labels := by rfl

def raw25691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw25691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25691 raw25691Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw25691 raw25691Labels = mixedMoment B raw25691step0 raw25691step0Labels := by
      have hz : ∀ j, raw25691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25691step0 = (fun i j => raw25691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25691step0 raw25691; decide +kernel
      have hl : raw25691step0Labels = raw25691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25691 raw25691Labels permutation346 hz
    mixedMoment B raw25691step0 raw25691step0Labels = mixedMoment B raw25691step1 raw25691step1Labels := by
      have ha : raw25691step1 = (fun i j => raw25691step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25691step1 raw25691step0; decide +kernel
      have hl : raw25691step1Labels = raw25691step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25691step0 raw25691step0Labels permutation33 permutation3
    _ = mixedMoment B node891 node891Labels := by rfl

def raw25692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw25692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25692 raw25692Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw25692 raw25692Labels = mixedMoment B raw25692step0 raw25692step0Labels := by
      have hz : ∀ j, raw25692 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25692step0 = (fun i j => raw25692 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25692step0 raw25692; decide +kernel
      have hl : raw25692step0Labels = raw25692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25692 raw25692Labels permutation265 hz
    mixedMoment B raw25692step0 raw25692step0Labels = mixedMoment B raw25692step1 raw25692step1Labels := by
      have ha : raw25692step1 = (fun i j => raw25692step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25692step1 raw25692step0; decide +kernel
      have hl : raw25692step1Labels = raw25692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25692step0 raw25692step0Labels permutation33 permutation3
    _ = mixedMoment B node891 node891Labels := by rfl

def raw25693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25693step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25693 raw25693Labels = mixedMoment B node559 node559Labels := by
  calc
    mixedMoment B raw25693 raw25693Labels = mixedMoment B raw25693step0 raw25693step0Labels := by
      have hz : ∀ j, raw25693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25693step0 = (fun i j => raw25693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25693step0 raw25693; decide +kernel
      have hl : raw25693step0Labels = raw25693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25693 raw25693Labels permutation346 hz
    mixedMoment B raw25693step0 raw25693step0Labels = mixedMoment B raw25693step1 raw25693step1Labels := by
      have hz : ∀ j, raw25693step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25693step1 = (fun i j => raw25693step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25693step1 raw25693step0; decide +kernel
      have hl : raw25693step1Labels = raw25693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25693step0 raw25693step0Labels permutation56 hz
    mixedMoment B raw25693step1 raw25693step1Labels = mixedMoment B raw25693step2 raw25693step2Labels := by
      have ha : raw25693step2 = (fun i j => raw25693step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25693step2 raw25693step1; decide +kernel
      have hl : raw25693step2Labels = raw25693step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25693step1 raw25693step1Labels permutation10 permutation3
    _ = mixedMoment B node559 node559Labels := by rfl

def raw25694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25694 raw25694Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw25694 raw25694Labels = mixedMoment B raw25694step0 raw25694step0Labels := by
      have hz : ∀ j, raw25694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25694step0 = (fun i j => raw25694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25694step0 raw25694; decide +kernel
      have hl : raw25694step0Labels = raw25694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25694 raw25694Labels permutation346 hz
    mixedMoment B raw25694step0 raw25694step0Labels = mixedMoment B raw25694step1 raw25694step1Labels := by
      have ha : raw25694step1 = (fun i j => raw25694step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25694step1 raw25694step0; decide +kernel
      have hl : raw25694step1Labels = raw25694step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25694step0 raw25694step0Labels permutation34 permutation3
    _ = mixedMoment B node887 node887Labels := by rfl

def raw25695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25695 raw25695Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw25695 raw25695Labels = mixedMoment B raw25695step0 raw25695step0Labels := by
      have hz : ∀ j, raw25695 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25695step0 = (fun i j => raw25695 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25695step0 raw25695; decide +kernel
      have hl : raw25695step0Labels = raw25695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25695 raw25695Labels permutation265 hz
    mixedMoment B raw25695step0 raw25695step0Labels = mixedMoment B raw25695step1 raw25695step1Labels := by
      have ha : raw25695step1 = (fun i j => raw25695step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25695step1 raw25695step0; decide +kernel
      have hl : raw25695step1Labels = raw25695step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25695step0 raw25695step0Labels permutation34 permutation3
    _ = mixedMoment B node887 node887Labels := by rfl

def raw25696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, -1, -2]]
def raw25696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw25696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw25696step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25696step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw25696step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25696step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw25696step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25696 raw25696Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw25696 raw25696Labels = mixedMoment B raw25696step0 raw25696step0Labels := by
      have hz : ∀ j, raw25696 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25696step0 = (fun i j => raw25696 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25696step0 raw25696; decide +kernel
      have hl : raw25696step0Labels = raw25696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25696 raw25696Labels permutation520 hz
    mixedMoment B raw25696step0 raw25696step0Labels = mixedMoment B raw25696step1 raw25696step1Labels := by
      have hz : ∀ j, raw25696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25696step1 = (fun i j => raw25696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25696step1 raw25696step0; decide +kernel
      have hl : raw25696step1Labels = raw25696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25696step0 raw25696step0Labels permutation80 hz
    mixedMoment B raw25696step1 raw25696step1Labels = mixedMoment B raw25696step2 raw25696step2Labels := by
      have hz : ∀ j, raw25696step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25696step2 = (fun i j => raw25696step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25696step2 raw25696step1; decide +kernel
      have hl : raw25696step2Labels = raw25696step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25696step1 raw25696step1Labels permutation14 hz
    mixedMoment B raw25696step2 raw25696step2Labels = mixedMoment B raw25696step3 raw25696step3Labels := by
      have ha : raw25696step3 = (fun i j => raw25696step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25696step3 raw25696step2; decide +kernel
      have hl : raw25696step3Labels = raw25696step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25696step2 raw25696step2Labels permutation2 permutation3
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw25697 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25697step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25697 raw25697Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw25697 raw25697Labels = mixedMoment B raw25697step0 raw25697step0Labels := by
      have hz : ∀ j, raw25697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25697step0 = (fun i j => raw25697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25697step0 raw25697; decide +kernel
      have hl : raw25697step0Labels = raw25697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25697 raw25697Labels permutation346 hz
    mixedMoment B raw25697step0 raw25697step0Labels = mixedMoment B raw25697step1 raw25697step1Labels := by
      have ha : raw25697step1 = (fun i j => raw25697step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25697step1 raw25697step0; decide +kernel
      have hl : raw25697step1Labels = raw25697step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25697step0 raw25697step0Labels permutation34 permutation6
    mixedMoment B raw25697step1 raw25697step1Labels = mixedMoment B raw25697step2 raw25697step2Labels := by
      have ha : raw25697step2 = raw25697step1 := by apply Matrix.ext; unfold raw25697step2 raw25697step1; decide +kernel
      have hl : raw25697step1Labels = labelEmbedding9 ∘ raw25697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25697step1 raw25697step1Labels raw25697step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw25698 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25698step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25698 raw25698Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw25698 raw25698Labels = mixedMoment B raw25698step0 raw25698step0Labels := by
      have hz : ∀ j, raw25698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25698step0 = (fun i j => raw25698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25698step0 raw25698; decide +kernel
      have hl : raw25698step0Labels = raw25698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25698 raw25698Labels permutation346 hz
    mixedMoment B raw25698step0 raw25698step0Labels = mixedMoment B raw25698step1 raw25698step1Labels := by
      have hz : ∀ j, raw25698step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25698step1 = (fun i j => raw25698step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25698step1 raw25698step0; decide +kernel
      have hl : raw25698step1Labels = raw25698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25698step0 raw25698step0Labels permutation56 hz
    mixedMoment B raw25698step1 raw25698step1Labels = mixedMoment B raw25698step2 raw25698step2Labels := by
      have ha : raw25698step2 = (fun i j => raw25698step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25698step2 raw25698step1; decide +kernel
      have hl : raw25698step2Labels = raw25698step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25698step1 raw25698step1Labels permutation8 permutation7
    mixedMoment B raw25698step2 raw25698step2Labels = mixedMoment B raw25698step3 raw25698step3Labels := by
      have ha : raw25698step3 = raw25698step2 := by apply Matrix.ext; unfold raw25698step3 raw25698step2; decide +kernel
      have hl : raw25698step2Labels = labelEmbedding10 ∘ raw25698step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25698step2 raw25698step2Labels raw25698step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw25699 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25699step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25699step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25699 raw25699Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw25699 raw25699Labels = mixedMoment B raw25699step0 raw25699step0Labels := by
      have hz : ∀ j, raw25699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25699step0 = (fun i j => raw25699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25699step0 raw25699; decide +kernel
      have hl : raw25699step0Labels = raw25699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25699 raw25699Labels permutation346 hz
    mixedMoment B raw25699step0 raw25699step0Labels = mixedMoment B raw25699step1 raw25699step1Labels := by
      have hz : ∀ j, raw25699step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25699step1 = (fun i j => raw25699step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25699step1 raw25699step0; decide +kernel
      have hl : raw25699step1Labels = raw25699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25699step0 raw25699step0Labels permutation56 hz
    mixedMoment B raw25699step1 raw25699step1Labels = mixedMoment B raw25699step2 raw25699step2Labels := by
      have ha : raw25699step2 = (fun i j => raw25699step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25699step2 raw25699step1; decide +kernel
      have hl : raw25699step2Labels = raw25699step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25699step1 raw25699step1Labels permutation8 permutation7
    mixedMoment B raw25699step2 raw25699step2Labels = mixedMoment B raw25699step3 raw25699step3Labels := by
      have ha : raw25699step3 = raw25699step2 := by apply Matrix.ext; unfold raw25699step3 raw25699step2; decide +kernel
      have hl : raw25699step2Labels = labelEmbedding10 ∘ raw25699step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25699step2 raw25699step2Labels raw25699step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw25700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25700step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25700 raw25700Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw25700 raw25700Labels = mixedMoment B raw25700step0 raw25700step0Labels := by
      have hz : ∀ j, raw25700 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25700step0 = (fun i j => raw25700 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25700step0 raw25700; decide +kernel
      have hl : raw25700step0Labels = raw25700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25700 raw25700Labels permutation265 hz
    mixedMoment B raw25700step0 raw25700step0Labels = mixedMoment B raw25700step1 raw25700step1Labels := by
      have ha : raw25700step1 = (fun i j => raw25700step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25700step1 raw25700step0; decide +kernel
      have hl : raw25700step1Labels = raw25700step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25700step0 raw25700step0Labels permutation34 permutation6
    mixedMoment B raw25700step1 raw25700step1Labels = mixedMoment B raw25700step2 raw25700step2Labels := by
      have ha : raw25700step2 = raw25700step1 := by apply Matrix.ext; unfold raw25700step2 raw25700step1; decide +kernel
      have hl : raw25700step1Labels = labelEmbedding9 ∘ raw25700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25700step1 raw25700step1Labels raw25700step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw25701 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25701step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25701 raw25701Labels = mixedMoment B node4400 node4400Labels := by
  calc
    mixedMoment B raw25701 raw25701Labels = mixedMoment B raw25701step0 raw25701step0Labels := by
      have ha : raw25701step0 = (fun i j => raw25701 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25701step0 raw25701; decide +kernel
      have hl : raw25701step0Labels = raw25701Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25701 raw25701Labels permutation154 permutation6
    mixedMoment B raw25701step0 raw25701step0Labels = mixedMoment B raw25701step1 raw25701step1Labels := by
      have ha : raw25701step1 = raw25701step0 := by apply Matrix.ext; unfold raw25701step1 raw25701step0; decide +kernel
      have hl : raw25701step0Labels = labelEmbedding9 ∘ raw25701step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25701step0 raw25701step0Labels raw25701step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4400 node4400Labels := by rfl

def raw25702 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25702step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25702 raw25702Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw25702 raw25702Labels = mixedMoment B raw25702step0 raw25702step0Labels := by
      have hz : ∀ j, raw25702 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25702step0 = (fun i j => raw25702 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25702step0 raw25702; decide +kernel
      have hl : raw25702step0Labels = raw25702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25702 raw25702Labels permutation265 hz
    mixedMoment B raw25702step0 raw25702step0Labels = mixedMoment B raw25702step1 raw25702step1Labels := by
      have ha : raw25702step1 = (fun i j => raw25702step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25702step1 raw25702step0; decide +kernel
      have hl : raw25702step1Labels = raw25702step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25702step0 raw25702step0Labels permutation34 permutation6
    mixedMoment B raw25702step1 raw25702step1Labels = mixedMoment B raw25702step2 raw25702step2Labels := by
      have ha : raw25702step2 = raw25702step1 := by apply Matrix.ext; unfold raw25702step2 raw25702step1; decide +kernel
      have hl : raw25702step1Labels = labelEmbedding9 ∘ raw25702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25702step1 raw25702step1Labels raw25702step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw25703 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25703step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25703 raw25703Labels = mixedMoment B node4462 node4462Labels := by
  calc
    mixedMoment B raw25703 raw25703Labels = mixedMoment B raw25703step0 raw25703step0Labels := by
      have hz : ∀ j, raw25703 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25703step0 = (fun i j => raw25703 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25703step0 raw25703; decide +kernel
      have hl : raw25703step0Labels = raw25703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25703 raw25703Labels permutation265 hz
    mixedMoment B raw25703step0 raw25703step0Labels = mixedMoment B raw25703step1 raw25703step1Labels := by
      have ha : raw25703step1 = (fun i j => raw25703step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25703step1 raw25703step0; decide +kernel
      have hl : raw25703step1Labels = raw25703step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25703step0 raw25703step0Labels permutation34 permutation6
    mixedMoment B raw25703step1 raw25703step1Labels = mixedMoment B raw25703step2 raw25703step2Labels := by
      have ha : raw25703step2 = raw25703step1 := by apply Matrix.ext; unfold raw25703step2 raw25703step1; decide +kernel
      have hl : raw25703step1Labels = labelEmbedding9 ∘ raw25703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25703step1 raw25703step1Labels raw25703step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4462 node4462Labels := by rfl

def raw25704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw25704step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw25704step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25704step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw25704step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25704 raw25704Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw25704 raw25704Labels = mixedMoment B raw25704step0 raw25704step0Labels := by
      have hz : ∀ j, raw25704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25704step0 = (fun i j => raw25704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25704step0 raw25704; decide +kernel
      have hl : raw25704step0Labels = raw25704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25704 raw25704Labels permutation346 hz
    mixedMoment B raw25704step0 raw25704step0Labels = mixedMoment B raw25704step1 raw25704step1Labels := by
      have hz : ∀ j, raw25704step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25704step1 = (fun i j => raw25704step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25704step1 raw25704step0; decide +kernel
      have hl : raw25704step1Labels = raw25704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25704step0 raw25704step0Labels permutation56 hz
    mixedMoment B raw25704step1 raw25704step1Labels = mixedMoment B raw25704step2 raw25704step2Labels := by
      have ha : raw25704step2 = (fun i j => raw25704step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25704step2 raw25704step1; decide +kernel
      have hl : raw25704step2Labels = raw25704step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25704step1 raw25704step1Labels permutation13 permutation4
    mixedMoment B raw25704step2 raw25704step2Labels = mixedMoment B raw25704step3 raw25704step3Labels := by
      have ha : raw25704step3 = -raw25704step2 := by apply Matrix.ext; change ∀ i j, raw25704step3 i j = -(raw25704step2 i j); unfold raw25704step3 raw25704step2; decide +kernel
      have hl : raw25704step3Labels = raw25704step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25704step3 raw25704step3Labels = mixedMoment B raw25704step4 raw25704step4Labels := by
      have ha : raw25704step4 = raw25704step3 := by apply Matrix.ext; unfold raw25704step4 raw25704step3; decide +kernel
      have hl : raw25704step3Labels = labelEmbedding7 ∘ raw25704step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25704step3 raw25704step3Labels raw25704step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

def raw25705 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25705step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25705step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25705 raw25705Labels = mixedMoment B node4425 node4425Labels := by
  calc
    mixedMoment B raw25705 raw25705Labels = mixedMoment B raw25705step0 raw25705step0Labels := by
      have hz : ∀ j, raw25705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25705step0 = (fun i j => raw25705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25705step0 raw25705; decide +kernel
      have hl : raw25705step0Labels = raw25705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25705 raw25705Labels permutation346 hz
    mixedMoment B raw25705step0 raw25705step0Labels = mixedMoment B raw25705step1 raw25705step1Labels := by
      have ha : raw25705step1 = (fun i j => raw25705step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25705step1 raw25705step0; decide +kernel
      have hl : raw25705step1Labels = raw25705step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25705step0 raw25705step0Labels permutation34 permutation6
    mixedMoment B raw25705step1 raw25705step1Labels = mixedMoment B raw25705step2 raw25705step2Labels := by
      have ha : raw25705step2 = raw25705step1 := by apply Matrix.ext; unfold raw25705step2 raw25705step1; decide +kernel
      have hl : raw25705step1Labels = labelEmbedding9 ∘ raw25705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25705step1 raw25705step1Labels raw25705step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4425 node4425Labels := by rfl

def raw25706 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25706step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25706 raw25706Labels = mixedMoment B node4425 node4425Labels := by
  calc
    mixedMoment B raw25706 raw25706Labels = mixedMoment B raw25706step0 raw25706step0Labels := by
      have hz : ∀ j, raw25706 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25706step0 = (fun i j => raw25706 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25706step0 raw25706; decide +kernel
      have hl : raw25706step0Labels = raw25706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25706 raw25706Labels permutation265 hz
    mixedMoment B raw25706step0 raw25706step0Labels = mixedMoment B raw25706step1 raw25706step1Labels := by
      have ha : raw25706step1 = (fun i j => raw25706step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25706step1 raw25706step0; decide +kernel
      have hl : raw25706step1Labels = raw25706step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25706step0 raw25706step0Labels permutation34 permutation6
    mixedMoment B raw25706step1 raw25706step1Labels = mixedMoment B raw25706step2 raw25706step2Labels := by
      have ha : raw25706step2 = raw25706step1 := by apply Matrix.ext; unfold raw25706step2 raw25706step1; decide +kernel
      have hl : raw25706step1Labels = labelEmbedding9 ∘ raw25706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25706step1 raw25706step1Labels raw25706step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4425 node4425Labels := by rfl

def raw25707 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25707step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25707step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25707 raw25707Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw25707 raw25707Labels = mixedMoment B raw25707step0 raw25707step0Labels := by
      have hz : ∀ j, raw25707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25707step0 = (fun i j => raw25707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25707step0 raw25707; decide +kernel
      have hl : raw25707step0Labels = raw25707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25707 raw25707Labels permutation346 hz
    mixedMoment B raw25707step0 raw25707step0Labels = mixedMoment B raw25707step1 raw25707step1Labels := by
      have hz : ∀ j, raw25707step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25707step1 = (fun i j => raw25707step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25707step1 raw25707step0; decide +kernel
      have hl : raw25707step1Labels = raw25707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25707step0 raw25707step0Labels permutation56 hz
    mixedMoment B raw25707step1 raw25707step1Labels = mixedMoment B raw25707step2 raw25707step2Labels := by
      have ha : raw25707step2 = (fun i j => raw25707step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25707step2 raw25707step1; decide +kernel
      have hl : raw25707step2Labels = raw25707step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25707step1 raw25707step1Labels permutation10 permutation6
    mixedMoment B raw25707step2 raw25707step2Labels = mixedMoment B raw25707step3 raw25707step3Labels := by
      have ha : raw25707step3 = raw25707step2 := by apply Matrix.ext; unfold raw25707step3 raw25707step2; decide +kernel
      have hl : raw25707step2Labels = labelEmbedding9 ∘ raw25707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25707step2 raw25707step2Labels raw25707step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw25708 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw25708step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw25708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25708 raw25708Labels = mixedMoment B node4504 node4504Labels := by
  calc
    mixedMoment B raw25708 raw25708Labels = mixedMoment B raw25708step0 raw25708step0Labels := by
      have hz : ∀ j, raw25708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25708step0 = (fun i j => raw25708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25708step0 raw25708; decide +kernel
      have hl : raw25708step0Labels = raw25708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25708 raw25708Labels permutation346 hz
    mixedMoment B raw25708step0 raw25708step0Labels = mixedMoment B raw25708step1 raw25708step1Labels := by
      have hz : ∀ j, raw25708step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25708step1 = (fun i j => raw25708step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25708step1 raw25708step0; decide +kernel
      have hl : raw25708step1Labels = raw25708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25708step0 raw25708step0Labels permutation56 hz
    mixedMoment B raw25708step1 raw25708step1Labels = mixedMoment B raw25708step2 raw25708step2Labels := by
      have ha : raw25708step2 = (fun i j => raw25708step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25708step2 raw25708step1; decide +kernel
      have hl : raw25708step2Labels = raw25708step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25708step1 raw25708step1Labels permutation10 permutation6
    mixedMoment B raw25708step2 raw25708step2Labels = mixedMoment B raw25708step3 raw25708step3Labels := by
      have ha : raw25708step3 = raw25708step2 := by apply Matrix.ext; unfold raw25708step3 raw25708step2; decide +kernel
      have hl : raw25708step2Labels = labelEmbedding9 ∘ raw25708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25708step2 raw25708step2Labels raw25708step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4504 node4504Labels := by rfl

def raw25709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw25709step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25709step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25709step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25709step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25709 raw25709Labels = mixedMoment B node4279 node4279Labels := by
  calc
    mixedMoment B raw25709 raw25709Labels = mixedMoment B raw25709step0 raw25709step0Labels := by
      have hz : ∀ j, raw25709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25709step0 = (fun i j => raw25709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25709step0 raw25709; decide +kernel
      have hl : raw25709step0Labels = raw25709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25709 raw25709Labels permutation346 hz
    mixedMoment B raw25709step0 raw25709step0Labels = mixedMoment B raw25709step1 raw25709step1Labels := by
      have hz : ∀ j, raw25709step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25709step1 = (fun i j => raw25709step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25709step1 raw25709step0; decide +kernel
      have hl : raw25709step1Labels = raw25709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25709step0 raw25709step0Labels permutation56 hz
    mixedMoment B raw25709step1 raw25709step1Labels = mixedMoment B raw25709step2 raw25709step2Labels := by
      have ha : raw25709step2 = (fun i j => raw25709step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25709step2 raw25709step1; decide +kernel
      have hl : raw25709step2Labels = raw25709step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25709step1 raw25709step1Labels permutation12 permutation4
    mixedMoment B raw25709step2 raw25709step2Labels = mixedMoment B raw25709step3 raw25709step3Labels := by
      have ha : raw25709step3 = -raw25709step2 := by apply Matrix.ext; change ∀ i j, raw25709step3 i j = -(raw25709step2 i j); unfold raw25709step3 raw25709step2; decide +kernel
      have hl : raw25709step3Labels = raw25709step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25709step3 raw25709step3Labels = mixedMoment B raw25709step4 raw25709step4Labels := by
      have ha : raw25709step4 = raw25709step3 := by apply Matrix.ext; unfold raw25709step4 raw25709step3; decide +kernel
      have hl : raw25709step3Labels = labelEmbedding7 ∘ raw25709step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25709step3 raw25709step3Labels raw25709step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4279 node4279Labels := by rfl

def raw25710 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25710step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25710 raw25710Labels = mixedMoment B node4427 node4427Labels := by
  calc
    mixedMoment B raw25710 raw25710Labels = mixedMoment B raw25710step0 raw25710step0Labels := by
      have hz : ∀ j, raw25710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25710step0 = (fun i j => raw25710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25710step0 raw25710; decide +kernel
      have hl : raw25710step0Labels = raw25710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25710 raw25710Labels permutation346 hz
    mixedMoment B raw25710step0 raw25710step0Labels = mixedMoment B raw25710step1 raw25710step1Labels := by
      have ha : raw25710step1 = (fun i j => raw25710step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25710step1 raw25710step0; decide +kernel
      have hl : raw25710step1Labels = raw25710step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25710step0 raw25710step0Labels permutation32 permutation6
    mixedMoment B raw25710step1 raw25710step1Labels = mixedMoment B raw25710step2 raw25710step2Labels := by
      have ha : raw25710step2 = raw25710step1 := by apply Matrix.ext; unfold raw25710step2 raw25710step1; decide +kernel
      have hl : raw25710step1Labels = labelEmbedding9 ∘ raw25710step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25710step1 raw25710step1Labels raw25710step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4427 node4427Labels := by rfl

def raw25711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25711step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25711step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25711 raw25711Labels = mixedMoment B node4427 node4427Labels := by
  calc
    mixedMoment B raw25711 raw25711Labels = mixedMoment B raw25711step0 raw25711step0Labels := by
      have hz : ∀ j, raw25711 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25711step0 = (fun i j => raw25711 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25711step0 raw25711; decide +kernel
      have hl : raw25711step0Labels = raw25711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25711 raw25711Labels permutation265 hz
    mixedMoment B raw25711step0 raw25711step0Labels = mixedMoment B raw25711step1 raw25711step1Labels := by
      have ha : raw25711step1 = (fun i j => raw25711step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25711step1 raw25711step0; decide +kernel
      have hl : raw25711step1Labels = raw25711step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25711step0 raw25711step0Labels permutation32 permutation6
    mixedMoment B raw25711step1 raw25711step1Labels = mixedMoment B raw25711step2 raw25711step2Labels := by
      have ha : raw25711step2 = raw25711step1 := by apply Matrix.ext; unfold raw25711step2 raw25711step1; decide +kernel
      have hl : raw25711step1Labels = labelEmbedding9 ∘ raw25711step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25711step1 raw25711step1Labels raw25711step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4427 node4427Labels := by rfl

def raw25712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25712step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25712step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25712step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25712 raw25712Labels = mixedMoment B node4506 node4506Labels := by
  calc
    mixedMoment B raw25712 raw25712Labels = mixedMoment B raw25712step0 raw25712step0Labels := by
      have hz : ∀ j, raw25712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25712step0 = (fun i j => raw25712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25712step0 raw25712; decide +kernel
      have hl : raw25712step0Labels = raw25712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25712 raw25712Labels permutation346 hz
    mixedMoment B raw25712step0 raw25712step0Labels = mixedMoment B raw25712step1 raw25712step1Labels := by
      have hz : ∀ j, raw25712step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25712step1 = (fun i j => raw25712step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25712step1 raw25712step0; decide +kernel
      have hl : raw25712step1Labels = raw25712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25712step0 raw25712step0Labels permutation56 hz
    mixedMoment B raw25712step1 raw25712step1Labels = mixedMoment B raw25712step2 raw25712step2Labels := by
      have ha : raw25712step2 = (fun i j => raw25712step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25712step2 raw25712step1; decide +kernel
      have hl : raw25712step2Labels = raw25712step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25712step1 raw25712step1Labels permutation8 permutation6
    mixedMoment B raw25712step2 raw25712step2Labels = mixedMoment B raw25712step3 raw25712step3Labels := by
      have ha : raw25712step3 = raw25712step2 := by apply Matrix.ext; unfold raw25712step3 raw25712step2; decide +kernel
      have hl : raw25712step2Labels = labelEmbedding9 ∘ raw25712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25712step2 raw25712step2Labels raw25712step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4506 node4506Labels := by rfl

def raw25713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25713step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25713step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25713step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25713step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25713 raw25713Labels = mixedMoment B node4283 node4283Labels := by
  calc
    mixedMoment B raw25713 raw25713Labels = mixedMoment B raw25713step0 raw25713step0Labels := by
      have hz : ∀ j, raw25713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25713step0 = (fun i j => raw25713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25713step0 raw25713; decide +kernel
      have hl : raw25713step0Labels = raw25713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25713 raw25713Labels permutation346 hz
    mixedMoment B raw25713step0 raw25713step0Labels = mixedMoment B raw25713step1 raw25713step1Labels := by
      have hz : ∀ j, raw25713step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25713step1 = (fun i j => raw25713step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25713step1 raw25713step0; decide +kernel
      have hl : raw25713step1Labels = raw25713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25713step0 raw25713step0Labels permutation56 hz
    mixedMoment B raw25713step1 raw25713step1Labels = mixedMoment B raw25713step2 raw25713step2Labels := by
      have ha : raw25713step2 = (fun i j => raw25713step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25713step2 raw25713step1; decide +kernel
      have hl : raw25713step2Labels = raw25713step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25713step1 raw25713step1Labels permutation11 permutation4
    mixedMoment B raw25713step2 raw25713step2Labels = mixedMoment B raw25713step3 raw25713step3Labels := by
      have ha : raw25713step3 = -raw25713step2 := by apply Matrix.ext; change ∀ i j, raw25713step3 i j = -(raw25713step2 i j); unfold raw25713step3 raw25713step2; decide +kernel
      have hl : raw25713step3Labels = raw25713step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25713step3 raw25713step3Labels = mixedMoment B raw25713step4 raw25713step4Labels := by
      have ha : raw25713step4 = raw25713step3 := by apply Matrix.ext; unfold raw25713step4 raw25713step3; decide +kernel
      have hl : raw25713step3Labels = labelEmbedding7 ∘ raw25713step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25713step3 raw25713step3Labels raw25713step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4283 node4283Labels := by rfl

def raw25714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25714step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25714step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25714 raw25714Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw25714 raw25714Labels = mixedMoment B raw25714step0 raw25714step0Labels := by
      have hz : ∀ j, raw25714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25714step0 = (fun i j => raw25714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25714step0 raw25714; decide +kernel
      have hl : raw25714step0Labels = raw25714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25714 raw25714Labels permutation346 hz
    mixedMoment B raw25714step0 raw25714step0Labels = mixedMoment B raw25714step1 raw25714step1Labels := by
      have ha : raw25714step1 = (fun i j => raw25714step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25714step1 raw25714step0; decide +kernel
      have hl : raw25714step1Labels = raw25714step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25714step0 raw25714step0Labels permutation34 permutation6
    mixedMoment B raw25714step1 raw25714step1Labels = mixedMoment B raw25714step2 raw25714step2Labels := by
      have ha : raw25714step2 = raw25714step1 := by apply Matrix.ext; unfold raw25714step2 raw25714step1; decide +kernel
      have hl : raw25714step1Labels = labelEmbedding9 ∘ raw25714step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25714step1 raw25714step1Labels raw25714step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw25715 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25715step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25715 raw25715Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw25715 raw25715Labels = mixedMoment B raw25715step0 raw25715step0Labels := by
      have hz : ∀ j, raw25715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25715step0 = (fun i j => raw25715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25715step0 raw25715; decide +kernel
      have hl : raw25715step0Labels = raw25715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25715 raw25715Labels permutation346 hz
    mixedMoment B raw25715step0 raw25715step0Labels = mixedMoment B raw25715step1 raw25715step1Labels := by
      have ha : raw25715step1 = (fun i j => raw25715step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25715step1 raw25715step0; decide +kernel
      have hl : raw25715step1Labels = raw25715step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25715step0 raw25715step0Labels permutation34 permutation6
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw25716 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25716step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25716step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25716 raw25716Labels = mixedMoment B node1302 node1302Labels := by
  calc
    mixedMoment B raw25716 raw25716Labels = mixedMoment B raw25716step0 raw25716step0Labels := by
      have hz : ∀ j, raw25716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25716step0 = (fun i j => raw25716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25716step0 raw25716; decide +kernel
      have hl : raw25716step0Labels = raw25716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25716 raw25716Labels permutation346 hz
    mixedMoment B raw25716step0 raw25716step0Labels = mixedMoment B raw25716step1 raw25716step1Labels := by
      have hz : ∀ j, raw25716step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25716step1 = (fun i j => raw25716step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25716step1 raw25716step0; decide +kernel
      have hl : raw25716step1Labels = raw25716step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25716step0 raw25716step0Labels permutation56 hz
    mixedMoment B raw25716step1 raw25716step1Labels = mixedMoment B raw25716step2 raw25716step2Labels := by
      have ha : raw25716step2 = (fun i j => raw25716step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25716step2 raw25716step1; decide +kernel
      have hl : raw25716step2Labels = raw25716step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25716step1 raw25716step1Labels permutation10 permutation6
    _ = mixedMoment B node1302 node1302Labels := by rfl

def raw25717 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25717step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25717 raw25717Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw25717 raw25717Labels = mixedMoment B raw25717step0 raw25717step0Labels := by
      have hz : ∀ j, raw25717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25717step0 = (fun i j => raw25717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25717step0 raw25717; decide +kernel
      have hl : raw25717step0Labels = raw25717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25717 raw25717Labels permutation346 hz
    mixedMoment B raw25717step0 raw25717step0Labels = mixedMoment B raw25717step1 raw25717step1Labels := by
      have hz : ∀ j, raw25717step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25717step1 = (fun i j => raw25717step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25717step1 raw25717step0; decide +kernel
      have hl : raw25717step1Labels = raw25717step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25717step0 raw25717step0Labels permutation56 hz
    mixedMoment B raw25717step1 raw25717step1Labels = mixedMoment B raw25717step2 raw25717step2Labels := by
      have ha : raw25717step2 = (fun i j => raw25717step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25717step2 raw25717step1; decide +kernel
      have hl : raw25717step2Labels = raw25717step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25717step1 raw25717step1Labels permutation10 permutation6
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw25718 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25718step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25718 raw25718Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw25718 raw25718Labels = mixedMoment B raw25718step0 raw25718step0Labels := by
      have hz : ∀ j, raw25718 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25718step0 = (fun i j => raw25718 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25718step0 raw25718; decide +kernel
      have hl : raw25718step0Labels = raw25718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25718 raw25718Labels permutation265 hz
    mixedMoment B raw25718step0 raw25718step0Labels = mixedMoment B raw25718step1 raw25718step1Labels := by
      have ha : raw25718step1 = (fun i j => raw25718step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25718step1 raw25718step0; decide +kernel
      have hl : raw25718step1Labels = raw25718step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25718step0 raw25718step0Labels permutation34 permutation6
    _ = mixedMoment B node811 node811Labels := by rfl

def raw25719 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25719 raw25719Labels = mixedMoment B node981 node981Labels := by
  calc
    mixedMoment B raw25719 raw25719Labels = mixedMoment B raw25719step0 raw25719step0Labels := by
      have ha : raw25719step0 = (fun i j => raw25719 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25719step0 raw25719; decide +kernel
      have hl : raw25719step0Labels = raw25719Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25719 raw25719Labels permutation154 permutation6
    _ = mixedMoment B node981 node981Labels := by rfl

def raw25720 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25720step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25720 raw25720Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw25720 raw25720Labels = mixedMoment B raw25720step0 raw25720step0Labels := by
      have hz : ∀ j, raw25720 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25720step0 = (fun i j => raw25720 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25720step0 raw25720; decide +kernel
      have hl : raw25720step0Labels = raw25720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25720 raw25720Labels permutation265 hz
    mixedMoment B raw25720step0 raw25720step0Labels = mixedMoment B raw25720step1 raw25720step1Labels := by
      have ha : raw25720step1 = (fun i j => raw25720step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25720step1 raw25720step0; decide +kernel
      have hl : raw25720step1Labels = raw25720step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25720step0 raw25720step0Labels permutation34 permutation6
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw25721 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25721step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25721 raw25721Labels = mixedMoment B node1045 node1045Labels := by
  calc
    mixedMoment B raw25721 raw25721Labels = mixedMoment B raw25721step0 raw25721step0Labels := by
      have hz : ∀ j, raw25721 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25721step0 = (fun i j => raw25721 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25721step0 raw25721; decide +kernel
      have hl : raw25721step0Labels = raw25721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25721 raw25721Labels permutation265 hz
    mixedMoment B raw25721step0 raw25721step0Labels = mixedMoment B raw25721step1 raw25721step1Labels := by
      have ha : raw25721step1 = (fun i j => raw25721step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25721step1 raw25721step0; decide +kernel
      have hl : raw25721step1Labels = raw25721step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25721step0 raw25721step0Labels permutation34 permutation6
    _ = mixedMoment B node1045 node1045Labels := by rfl

def raw25722 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25722step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25722step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25722 raw25722Labels = mixedMoment B node857 node857Labels := by
  calc
    mixedMoment B raw25722 raw25722Labels = mixedMoment B raw25722step0 raw25722step0Labels := by
      have hz : ∀ j, raw25722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25722step0 = (fun i j => raw25722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25722step0 raw25722; decide +kernel
      have hl : raw25722step0Labels = raw25722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25722 raw25722Labels permutation346 hz
    mixedMoment B raw25722step0 raw25722step0Labels = mixedMoment B raw25722step1 raw25722step1Labels := by
      have hz : ∀ j, raw25722step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25722step1 = (fun i j => raw25722step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25722step1 raw25722step0; decide +kernel
      have hl : raw25722step1Labels = raw25722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25722step0 raw25722step0Labels permutation56 hz
    mixedMoment B raw25722step1 raw25722step1Labels = mixedMoment B raw25722step2 raw25722step2Labels := by
      have ha : raw25722step2 = (fun i j => raw25722step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25722step2 raw25722step1; decide +kernel
      have hl : raw25722step2Labels = raw25722step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25722step1 raw25722step1Labels permutation10 permutation6
    _ = mixedMoment B node857 node857Labels := by rfl

def raw25723 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25723step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25723 raw25723Labels = mixedMoment B node1006 node1006Labels := by
  calc
    mixedMoment B raw25723 raw25723Labels = mixedMoment B raw25723step0 raw25723step0Labels := by
      have hz : ∀ j, raw25723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25723step0 = (fun i j => raw25723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25723step0 raw25723; decide +kernel
      have hl : raw25723step0Labels = raw25723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25723 raw25723Labels permutation346 hz
    mixedMoment B raw25723step0 raw25723step0Labels = mixedMoment B raw25723step1 raw25723step1Labels := by
      have ha : raw25723step1 = (fun i j => raw25723step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25723step1 raw25723step0; decide +kernel
      have hl : raw25723step1Labels = raw25723step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25723step0 raw25723step0Labels permutation34 permutation6
    _ = mixedMoment B node1006 node1006Labels := by rfl

def raw25724 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25724step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25724 raw25724Labels = mixedMoment B node1006 node1006Labels := by
  calc
    mixedMoment B raw25724 raw25724Labels = mixedMoment B raw25724step0 raw25724step0Labels := by
      have hz : ∀ j, raw25724 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25724step0 = (fun i j => raw25724 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25724step0 raw25724; decide +kernel
      have hl : raw25724step0Labels = raw25724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25724 raw25724Labels permutation265 hz
    mixedMoment B raw25724step0 raw25724step0Labels = mixedMoment B raw25724step1 raw25724step1Labels := by
      have ha : raw25724step1 = (fun i j => raw25724step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25724step1 raw25724step0; decide +kernel
      have hl : raw25724step1Labels = raw25724step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25724step0 raw25724step0Labels permutation34 permutation6
    _ = mixedMoment B node1006 node1006Labels := by rfl

def raw25725 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25725step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25725step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25725 raw25725Labels = mixedMoment B node1084 node1084Labels := by
  calc
    mixedMoment B raw25725 raw25725Labels = mixedMoment B raw25725step0 raw25725step0Labels := by
      have hz : ∀ j, raw25725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25725step0 = (fun i j => raw25725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25725step0 raw25725; decide +kernel
      have hl : raw25725step0Labels = raw25725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25725 raw25725Labels permutation346 hz
    mixedMoment B raw25725step0 raw25725step0Labels = mixedMoment B raw25725step1 raw25725step1Labels := by
      have hz : ∀ j, raw25725step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25725step1 = (fun i j => raw25725step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25725step1 raw25725step0; decide +kernel
      have hl : raw25725step1Labels = raw25725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25725step0 raw25725step0Labels permutation56 hz
    mixedMoment B raw25725step1 raw25725step1Labels = mixedMoment B raw25725step2 raw25725step2Labels := by
      have ha : raw25725step2 = (fun i j => raw25725step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25725step2 raw25725step1; decide +kernel
      have hl : raw25725step2Labels = raw25725step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25725step1 raw25725step1Labels permutation10 permutation6
    _ = mixedMoment B node1084 node1084Labels := by rfl

def raw25726 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25726step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25726step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw25726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25726 raw25726Labels = mixedMoment B node1088 node1088Labels := by
  calc
    mixedMoment B raw25726 raw25726Labels = mixedMoment B raw25726step0 raw25726step0Labels := by
      have hz : ∀ j, raw25726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25726step0 = (fun i j => raw25726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25726step0 raw25726; decide +kernel
      have hl : raw25726step0Labels = raw25726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25726 raw25726Labels permutation346 hz
    mixedMoment B raw25726step0 raw25726step0Labels = mixedMoment B raw25726step1 raw25726step1Labels := by
      have hz : ∀ j, raw25726step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25726step1 = (fun i j => raw25726step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25726step1 raw25726step0; decide +kernel
      have hl : raw25726step1Labels = raw25726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25726step0 raw25726step0Labels permutation56 hz
    mixedMoment B raw25726step1 raw25726step1Labels = mixedMoment B raw25726step2 raw25726step2Labels := by
      have ha : raw25726step2 = (fun i j => raw25726step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25726step2 raw25726step1; decide +kernel
      have hl : raw25726step2Labels = raw25726step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25726step1 raw25726step1Labels permutation10 permutation6
    _ = mixedMoment B node1088 node1088Labels := by rfl

def raw25727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25727step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25727step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25727 raw25727Labels = mixedMoment B node858 node858Labels := by
  calc
    mixedMoment B raw25727 raw25727Labels = mixedMoment B raw25727step0 raw25727step0Labels := by
      have hz : ∀ j, raw25727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25727step0 = (fun i j => raw25727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25727step0 raw25727; decide +kernel
      have hl : raw25727step0Labels = raw25727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25727 raw25727Labels permutation346 hz
    mixedMoment B raw25727step0 raw25727step0Labels = mixedMoment B raw25727step1 raw25727step1Labels := by
      have hz : ∀ j, raw25727step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25727step1 = (fun i j => raw25727step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25727step1 raw25727step0; decide +kernel
      have hl : raw25727step1Labels = raw25727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25727step0 raw25727step0Labels permutation56 hz
    mixedMoment B raw25727step1 raw25727step1Labels = mixedMoment B raw25727step2 raw25727step2Labels := by
      have ha : raw25727step2 = (fun i j => raw25727step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25727step2 raw25727step1; decide +kernel
      have hl : raw25727step2Labels = raw25727step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25727step1 raw25727step1Labels permutation8 permutation6
    _ = mixedMoment B node858 node858Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
