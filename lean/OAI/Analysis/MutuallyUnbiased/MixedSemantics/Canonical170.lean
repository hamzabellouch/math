import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21760 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21760 raw21760Labels = mixedMoment B node983 node983Labels := by
  calc
    mixedMoment B raw21760 raw21760Labels = mixedMoment B raw21760step0 raw21760step0Labels := by
      have hz : ∀ j, raw21760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21760step0 = (fun i j => raw21760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21760step0 raw21760; decide +kernel
      have hl : raw21760step0Labels = raw21760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21760 raw21760Labels permutation346 hz
    mixedMoment B raw21760step0 raw21760step0Labels = mixedMoment B raw21760step1 raw21760step1Labels := by
      have ha : raw21760step1 = (fun i j => raw21760step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21760step1 raw21760step0; decide +kernel
      have hl : raw21760step1Labels = raw21760step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21760step0 raw21760step0Labels permutation32 permutation6
    _ = mixedMoment B node983 node983Labels := by rfl

def raw21761 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21761step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21761 raw21761Labels = mixedMoment B node983 node983Labels := by
  calc
    mixedMoment B raw21761 raw21761Labels = mixedMoment B raw21761step0 raw21761step0Labels := by
      have hz : ∀ j, raw21761 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21761step0 = (fun i j => raw21761 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21761step0 raw21761; decide +kernel
      have hl : raw21761step0Labels = raw21761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21761 raw21761Labels permutation265 hz
    mixedMoment B raw21761step0 raw21761step0Labels = mixedMoment B raw21761step1 raw21761step1Labels := by
      have ha : raw21761step1 = (fun i j => raw21761step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21761step1 raw21761step0; decide +kernel
      have hl : raw21761step1Labels = raw21761step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21761step0 raw21761step0Labels permutation32 permutation6
    _ = mixedMoment B node983 node983Labels := by rfl

def raw21762 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21762step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21762 raw21762Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw21762 raw21762Labels = mixedMoment B raw21762step0 raw21762step0Labels := by
      have hz : ∀ j, raw21762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21762step0 = (fun i j => raw21762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21762step0 raw21762; decide +kernel
      have hl : raw21762step0Labels = raw21762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21762 raw21762Labels permutation346 hz
    mixedMoment B raw21762step0 raw21762step0Labels = mixedMoment B raw21762step1 raw21762step1Labels := by
      have hz : ∀ j, raw21762step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21762step1 = (fun i j => raw21762step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21762step1 raw21762step0; decide +kernel
      have hl : raw21762step1Labels = raw21762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21762step0 raw21762step0Labels permutation56 hz
    mixedMoment B raw21762step1 raw21762step1Labels = mixedMoment B raw21762step2 raw21762step2Labels := by
      have ha : raw21762step2 = (fun i j => raw21762step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21762step2 raw21762step1; decide +kernel
      have hl : raw21762step2Labels = raw21762step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21762step1 raw21762step1Labels permutation8 permutation6
    _ = mixedMoment B node1047 node1047Labels := by rfl

def raw21763 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21763step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21763step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21763step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![-2, -1, 3]]
def raw21763step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21763step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw21763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21763 raw21763Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw21763 raw21763Labels = mixedMoment B raw21763step0 raw21763step0Labels := by
      have hz : ∀ j, raw21763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21763step0 = (fun i j => raw21763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21763step0 raw21763; decide +kernel
      have hl : raw21763step0Labels = raw21763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21763 raw21763Labels permutation434 hz
    mixedMoment B raw21763step0 raw21763step0Labels = mixedMoment B raw21763step1 raw21763step1Labels := by
      have hz : ∀ j, raw21763step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21763step1 = (fun i j => raw21763step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21763step1 raw21763step0; decide +kernel
      have hl : raw21763step1Labels = raw21763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21763step0 raw21763step0Labels permutation80 hz
    mixedMoment B raw21763step1 raw21763step1Labels = mixedMoment B raw21763step2 raw21763step2Labels := by
      have hz : ∀ j, raw21763step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21763step2 = (fun i j => raw21763step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21763step2 raw21763step1; decide +kernel
      have hl : raw21763step2Labels = raw21763step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21763step1 raw21763step1Labels permutation14 hz
    mixedMoment B raw21763step2 raw21763step2Labels = mixedMoment B raw21763step3 raw21763step3Labels := by
      have ha : raw21763step3 = (fun i j => raw21763step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21763step3 raw21763step2; decide +kernel
      have hl : raw21763step3Labels = raw21763step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21763step2 raw21763step2Labels permutation2 permutation6
    _ = mixedMoment B node860 node860Labels := by rfl

def raw21764 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21764step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21764 raw21764Labels = mixedMoment B node1010 node1010Labels := by
  calc
    mixedMoment B raw21764 raw21764Labels = mixedMoment B raw21764step0 raw21764step0Labels := by
      have hz : ∀ j, raw21764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21764step0 = (fun i j => raw21764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21764step0 raw21764; decide +kernel
      have hl : raw21764step0Labels = raw21764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21764 raw21764Labels permutation434 hz
    mixedMoment B raw21764step0 raw21764step0Labels = mixedMoment B raw21764step1 raw21764step1Labels := by
      have hz : ∀ j, raw21764step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21764step1 = (fun i j => raw21764step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21764step1 raw21764step0; decide +kernel
      have hl : raw21764step1Labels = raw21764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21764step0 raw21764step0Labels permutation80 hz
    mixedMoment B raw21764step1 raw21764step1Labels = mixedMoment B raw21764step2 raw21764step2Labels := by
      have ha : raw21764step2 = (fun i j => raw21764step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21764step2 raw21764step1; decide +kernel
      have hl : raw21764step2Labels = raw21764step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21764step1 raw21764step1Labels permutation8 permutation6
    _ = mixedMoment B node1010 node1010Labels := by rfl

def raw21765 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21765step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21765 raw21765Labels = mixedMoment B node1010 node1010Labels := by
  calc
    mixedMoment B raw21765 raw21765Labels = mixedMoment B raw21765step0 raw21765step0Labels := by
      have hz : ∀ j, raw21765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21765step0 = (fun i j => raw21765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21765step0 raw21765; decide +kernel
      have hl : raw21765step0Labels = raw21765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21765 raw21765Labels permutation434 hz
    mixedMoment B raw21765step0 raw21765step0Labels = mixedMoment B raw21765step1 raw21765step1Labels := by
      have hz : ∀ j, raw21765step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21765step1 = (fun i j => raw21765step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21765step1 raw21765step0; decide +kernel
      have hl : raw21765step1Labels = raw21765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21765step0 raw21765step0Labels permutation56 hz
    mixedMoment B raw21765step1 raw21765step1Labels = mixedMoment B raw21765step2 raw21765step2Labels := by
      have ha : raw21765step2 = (fun i j => raw21765step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21765step2 raw21765step1; decide +kernel
      have hl : raw21765step2Labels = raw21765step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21765step1 raw21765step1Labels permutation8 permutation6
    _ = mixedMoment B node1010 node1010Labels := by rfl

def raw21766 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21766step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw21766step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21766 raw21766Labels = mixedMoment B node1010 node1010Labels := by
  calc
    mixedMoment B raw21766 raw21766Labels = mixedMoment B raw21766step0 raw21766step0Labels := by
      have hz : ∀ j, raw21766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21766step0 = (fun i j => raw21766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21766step0 raw21766; decide +kernel
      have hl : raw21766step0Labels = raw21766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21766 raw21766Labels permutation346 hz
    mixedMoment B raw21766step0 raw21766step0Labels = mixedMoment B raw21766step1 raw21766step1Labels := by
      have hz : ∀ j, raw21766step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21766step1 = (fun i j => raw21766step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21766step1 raw21766step0; decide +kernel
      have hl : raw21766step1Labels = raw21766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21766step0 raw21766step0Labels permutation56 hz
    mixedMoment B raw21766step1 raw21766step1Labels = mixedMoment B raw21766step2 raw21766step2Labels := by
      have ha : raw21766step2 = (fun i j => raw21766step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21766step2 raw21766step1; decide +kernel
      have hl : raw21766step2Labels = raw21766step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21766step1 raw21766step1Labels permutation8 permutation6
    _ = mixedMoment B node1010 node1010Labels := by rfl

def raw21767 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw21767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw21767step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw21767step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21767step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-3, 0, 3]]
def raw21767step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21767step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw21767step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21767 raw21767Labels = mixedMoment B node1092 node1092Labels := by
  calc
    mixedMoment B raw21767 raw21767Labels = mixedMoment B raw21767step0 raw21767step0Labels := by
      have hz : ∀ j, raw21767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21767step0 = (fun i j => raw21767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21767step0 raw21767; decide +kernel
      have hl : raw21767step0Labels = raw21767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21767 raw21767Labels permutation434 hz
    mixedMoment B raw21767step0 raw21767step0Labels = mixedMoment B raw21767step1 raw21767step1Labels := by
      have hz : ∀ j, raw21767step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21767step1 = (fun i j => raw21767step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21767step1 raw21767step0; decide +kernel
      have hl : raw21767step1Labels = raw21767step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21767step0 raw21767step0Labels permutation80 hz
    mixedMoment B raw21767step1 raw21767step1Labels = mixedMoment B raw21767step2 raw21767step2Labels := by
      have hz : ∀ j, raw21767step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21767step2 = (fun i j => raw21767step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21767step2 raw21767step1; decide +kernel
      have hl : raw21767step2Labels = raw21767step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21767step1 raw21767step1Labels permutation14 hz
    mixedMoment B raw21767step2 raw21767step2Labels = mixedMoment B raw21767step3 raw21767step3Labels := by
      have ha : raw21767step3 = (fun i j => raw21767step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21767step3 raw21767step2; decide +kernel
      have hl : raw21767step3Labels = raw21767step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21767step2 raw21767step2Labels permutation2 permutation6
    _ = mixedMoment B node1092 node1092Labels := by rfl

def raw21768 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21768step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21768step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21768step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-1, -2, 3]]
def raw21768step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21768step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw21768step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21768 raw21768Labels = mixedMoment B node859 node859Labels := by
  calc
    mixedMoment B raw21768 raw21768Labels = mixedMoment B raw21768step0 raw21768step0Labels := by
      have hz : ∀ j, raw21768 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21768step0 = (fun i j => raw21768 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21768step0 raw21768; decide +kernel
      have hl : raw21768step0Labels = raw21768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21768 raw21768Labels permutation434 hz
    mixedMoment B raw21768step0 raw21768step0Labels = mixedMoment B raw21768step1 raw21768step1Labels := by
      have hz : ∀ j, raw21768step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21768step1 = (fun i j => raw21768step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21768step1 raw21768step0; decide +kernel
      have hl : raw21768step1Labels = raw21768step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21768step0 raw21768step0Labels permutation80 hz
    mixedMoment B raw21768step1 raw21768step1Labels = mixedMoment B raw21768step2 raw21768step2Labels := by
      have hz : ∀ j, raw21768step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21768step2 = (fun i j => raw21768step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21768step2 raw21768step1; decide +kernel
      have hl : raw21768step2Labels = raw21768step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21768step1 raw21768step1Labels permutation14 hz
    mixedMoment B raw21768step2 raw21768step2Labels = mixedMoment B raw21768step3 raw21768step3Labels := by
      have ha : raw21768step3 = (fun i j => raw21768step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21768step3 raw21768step2; decide +kernel
      have hl : raw21768step3Labels = raw21768step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21768step2 raw21768step2Labels permutation2 permutation6
    _ = mixedMoment B node859 node859Labels := by rfl

def raw21769 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21769step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21769 raw21769Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw21769 raw21769Labels = mixedMoment B raw21769step0 raw21769step0Labels := by
      have hz : ∀ j, raw21769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21769step0 = (fun i j => raw21769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21769step0 raw21769; decide +kernel
      have hl : raw21769step0Labels = raw21769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21769 raw21769Labels permutation434 hz
    mixedMoment B raw21769step0 raw21769step0Labels = mixedMoment B raw21769step1 raw21769step1Labels := by
      have hz : ∀ j, raw21769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21769step1 = (fun i j => raw21769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21769step1 raw21769step0; decide +kernel
      have hl : raw21769step1Labels = raw21769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21769step0 raw21769step0Labels permutation80 hz
    mixedMoment B raw21769step1 raw21769step1Labels = mixedMoment B raw21769step2 raw21769step2Labels := by
      have ha : raw21769step2 = (fun i j => raw21769step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21769step2 raw21769step1; decide +kernel
      have hl : raw21769step2Labels = raw21769step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21769step1 raw21769step1Labels permutation8 permutation6
    _ = mixedMoment B node1009 node1009Labels := by rfl

def raw21770 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21770step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21770step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21770step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21770 raw21770Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw21770 raw21770Labels = mixedMoment B raw21770step0 raw21770step0Labels := by
      have hz : ∀ j, raw21770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21770step0 = (fun i j => raw21770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21770step0 raw21770; decide +kernel
      have hl : raw21770step0Labels = raw21770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21770 raw21770Labels permutation434 hz
    mixedMoment B raw21770step0 raw21770step0Labels = mixedMoment B raw21770step1 raw21770step1Labels := by
      have hz : ∀ j, raw21770step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21770step1 = (fun i j => raw21770step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21770step1 raw21770step0; decide +kernel
      have hl : raw21770step1Labels = raw21770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21770step0 raw21770step0Labels permutation56 hz
    mixedMoment B raw21770step1 raw21770step1Labels = mixedMoment B raw21770step2 raw21770step2Labels := by
      have ha : raw21770step2 = (fun i j => raw21770step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21770step2 raw21770step1; decide +kernel
      have hl : raw21770step2Labels = raw21770step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21770step1 raw21770step1Labels permutation8 permutation6
    _ = mixedMoment B node1009 node1009Labels := by rfl

def raw21771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21771 raw21771Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw21771 raw21771Labels = mixedMoment B raw21771step0 raw21771step0Labels := by
      have hz : ∀ j, raw21771 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21771step0 = (fun i j => raw21771 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21771step0 raw21771; decide +kernel
      have hl : raw21771step0Labels = raw21771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21771 raw21771Labels permutation434 hz
    mixedMoment B raw21771step0 raw21771step0Labels = mixedMoment B raw21771step1 raw21771step1Labels := by
      have hz : ∀ j, raw21771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21771step1 = (fun i j => raw21771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21771step1 raw21771step0; decide +kernel
      have hl : raw21771step1Labels = raw21771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21771step0 raw21771step0Labels permutation80 hz
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw21772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21772 raw21772Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw21772 raw21772Labels = mixedMoment B raw21772step0 raw21772step0Labels := by
      have hz : ∀ j, raw21772 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21772step0 = (fun i j => raw21772 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21772step0 raw21772; decide +kernel
      have hl : raw21772step0Labels = raw21772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21772 raw21772Labels permutation434 hz
    mixedMoment B raw21772step0 raw21772step0Labels = mixedMoment B raw21772step1 raw21772step1Labels := by
      have hz : ∀ j, raw21772step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21772step1 = (fun i j => raw21772step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21772step1 raw21772step0; decide +kernel
      have hl : raw21772step1Labels = raw21772step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21772step0 raw21772step0Labels permutation56 hz
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw21773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21773 raw21773Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw21773 raw21773Labels = mixedMoment B raw21773step0 raw21773step0Labels := by
      have hz : ∀ j, raw21773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21773step0 = (fun i j => raw21773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21773step0 raw21773; decide +kernel
      have hl : raw21773step0Labels = raw21773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21773 raw21773Labels permutation346 hz
    mixedMoment B raw21773step0 raw21773step0Labels = mixedMoment B raw21773step1 raw21773step1Labels := by
      have hz : ∀ j, raw21773step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21773step1 = (fun i j => raw21773step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21773step1 raw21773step0; decide +kernel
      have hl : raw21773step1Labels = raw21773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21773step0 raw21773step0Labels permutation56 hz
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw21774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21774step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21774 raw21774Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw21774 raw21774Labels = mixedMoment B raw21774step0 raw21774step0Labels := by
      have hz : ∀ j, raw21774 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21774step0 = (fun i j => raw21774 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21774step0 raw21774; decide +kernel
      have hl : raw21774step0Labels = raw21774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21774 raw21774Labels permutation434 hz
    mixedMoment B raw21774step0 raw21774step0Labels = mixedMoment B raw21774step1 raw21774step1Labels := by
      have hz : ∀ j, raw21774step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21774step1 = (fun i j => raw21774step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21774step1 raw21774step0; decide +kernel
      have hl : raw21774step1Labels = raw21774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21774step0 raw21774step0Labels permutation80 hz
    mixedMoment B raw21774step1 raw21774step1Labels = mixedMoment B raw21774step2 raw21774step2Labels := by
      have hz : ∀ j, raw21774step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21774step2 = (fun i j => raw21774step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21774step2 raw21774step1; decide +kernel
      have hl : raw21774step2Labels = raw21774step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21774step1 raw21774step1Labels permutation14 hz
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw21775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21775step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![2, 0, -2]]
def raw21775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21775step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw21775step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw21775step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw21775step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21775 raw21775Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw21775 raw21775Labels = mixedMoment B raw21775step0 raw21775step0Labels := by
      have hz : ∀ j, raw21775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21775step0 = (fun i j => raw21775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21775step0 raw21775; decide +kernel
      have hl : raw21775step0Labels = raw21775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21775 raw21775Labels permutation434 hz
    mixedMoment B raw21775step0 raw21775step0Labels = mixedMoment B raw21775step1 raw21775step1Labels := by
      have hz : ∀ j, raw21775step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21775step1 = (fun i j => raw21775step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21775step1 raw21775step0; decide +kernel
      have hl : raw21775step1Labels = raw21775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21775step0 raw21775step0Labels permutation80 hz
    mixedMoment B raw21775step1 raw21775step1Labels = mixedMoment B raw21775step2 raw21775step2Labels := by
      have hz : ∀ j, raw21775step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21775step2 = (fun i j => raw21775step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21775step2 raw21775step1; decide +kernel
      have hl : raw21775step2Labels = raw21775step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21775step1 raw21775step1Labels permutation14 hz
    mixedMoment B raw21775step2 raw21775step2Labels = mixedMoment B raw21775step3 raw21775step3Labels := by
      have hz : ∀ i, raw21775step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw21775step3 = (fun i j => raw21775step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw21775step3 raw21775step2; decide +kernel
      have hl : raw21775step3Labels = (fun j => raw21775step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw21775step2 raw21775step2Labels permutation4 hz
    mixedMoment B raw21775step3 raw21775step3Labels = mixedMoment B raw21775step4 raw21775step4Labels := by
      have ha : raw21775step4 = raw21775step3 := by apply Matrix.ext; unfold raw21775step4 raw21775step3; decide +kernel
      have hl : raw21775step3Labels = labelEmbedding2 ∘ raw21775step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21775step3 raw21775step3Labels raw21775step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw21776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21776 raw21776Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw21776 raw21776Labels = mixedMoment B raw21776step0 raw21776step0Labels := by
      have hz : ∀ j, raw21776 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21776step0 = (fun i j => raw21776 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21776step0 raw21776; decide +kernel
      have hl : raw21776step0Labels = raw21776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21776 raw21776Labels permutation434 hz
    mixedMoment B raw21776step0 raw21776step0Labels = mixedMoment B raw21776step1 raw21776step1Labels := by
      have hz : ∀ j, raw21776step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21776step1 = (fun i j => raw21776step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21776step1 raw21776step0; decide +kernel
      have hl : raw21776step1Labels = raw21776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21776step0 raw21776step0Labels permutation80 hz
    _ = mixedMoment B node4177 node4177Labels := by rfl

def raw21777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21777 raw21777Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21777 raw21777Labels = mixedMoment B raw21777step0 raw21777step0Labels := by
      have hz : ∀ j, raw21777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21777step0 = (fun i j => raw21777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21777step0 raw21777; decide +kernel
      have hl : raw21777step0Labels = raw21777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21777 raw21777Labels permutation434 hz
    mixedMoment B raw21777step0 raw21777step0Labels = mixedMoment B raw21777step1 raw21777step1Labels := by
      have ha : raw21777step1 = (fun i j => raw21777step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21777step1 raw21777step0; decide +kernel
      have hl : raw21777step1Labels = raw21777step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21777step0 raw21777step0Labels permutation38 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw21778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21778 raw21778Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21778 raw21778Labels = mixedMoment B raw21778step0 raw21778step0Labels := by
      have hz : ∀ j, raw21778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21778step0 = (fun i j => raw21778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21778step0 raw21778; decide +kernel
      have hl : raw21778step0Labels = raw21778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21778 raw21778Labels permutation346 hz
    mixedMoment B raw21778step0 raw21778step0Labels = mixedMoment B raw21778step1 raw21778step1Labels := by
      have ha : raw21778step1 = (fun i j => raw21778step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21778step1 raw21778step0; decide +kernel
      have hl : raw21778step1Labels = raw21778step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21778step0 raw21778step0Labels permutation38 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw21779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21779 raw21779Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw21779 raw21779Labels = mixedMoment B raw21779step0 raw21779step0Labels := by
      have hz : ∀ j, raw21779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21779step0 = (fun i j => raw21779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21779step0 raw21779; decide +kernel
      have hl : raw21779step0Labels = raw21779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21779 raw21779Labels permutation434 hz
    mixedMoment B raw21779step0 raw21779step0Labels = mixedMoment B raw21779step1 raw21779step1Labels := by
      have hz : ∀ j, raw21779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21779step1 = (fun i j => raw21779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21779step1 raw21779step0; decide +kernel
      have hl : raw21779step1Labels = raw21779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21779step0 raw21779step0Labels permutation80 hz
    mixedMoment B raw21779step1 raw21779step1Labels = mixedMoment B raw21779step2 raw21779step2Labels := by
      have ha : raw21779step2 = (fun i j => raw21779step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21779step2 raw21779step1; decide +kernel
      have hl : raw21779step2Labels = raw21779step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21779step1 raw21779step1Labels permutation10 permutation2
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw21780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21780 raw21780Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw21780 raw21780Labels = mixedMoment B raw21780step0 raw21780step0Labels := by
      have hz : ∀ j, raw21780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21780step0 = (fun i j => raw21780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21780step0 raw21780; decide +kernel
      have hl : raw21780step0Labels = raw21780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21780 raw21780Labels permutation434 hz
    mixedMoment B raw21780step0 raw21780step0Labels = mixedMoment B raw21780step1 raw21780step1Labels := by
      have hz : ∀ j, raw21780step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21780step1 = (fun i j => raw21780step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21780step1 raw21780step0; decide +kernel
      have hl : raw21780step1Labels = raw21780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21780step0 raw21780step0Labels permutation80 hz
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw21781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21781step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21781 raw21781Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw21781 raw21781Labels = mixedMoment B raw21781step0 raw21781step0Labels := by
      have hz : ∀ j, raw21781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21781step0 = (fun i j => raw21781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21781step0 raw21781; decide +kernel
      have hl : raw21781step0Labels = raw21781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21781 raw21781Labels permutation434 hz
    mixedMoment B raw21781step0 raw21781step0Labels = mixedMoment B raw21781step1 raw21781step1Labels := by
      have hz : ∀ j, raw21781step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21781step1 = (fun i j => raw21781step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21781step1 raw21781step0; decide +kernel
      have hl : raw21781step1Labels = raw21781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21781step0 raw21781step0Labels permutation56 hz
    _ = mixedMoment B node4177 node4177Labels := by rfl

def raw21782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21782 raw21782Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21782 raw21782Labels = mixedMoment B raw21782step0 raw21782step0Labels := by
      have hz : ∀ j, raw21782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21782step0 = (fun i j => raw21782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21782step0 raw21782; decide +kernel
      have hl : raw21782step0Labels = raw21782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21782 raw21782Labels permutation434 hz
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw21783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21783 raw21783Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21783 raw21783Labels = mixedMoment B raw21783step0 raw21783step0Labels := by
      have hz : ∀ j, raw21783 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21783step0 = (fun i j => raw21783 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21783step0 raw21783; decide +kernel
      have hl : raw21783step0Labels = raw21783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21783 raw21783Labels permutation265 hz
    mixedMoment B raw21783step0 raw21783step0Labels = mixedMoment B raw21783step1 raw21783step1Labels := by
      have ha : raw21783step1 = (fun i j => raw21783step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21783step1 raw21783step0; decide +kernel
      have hl : raw21783step1Labels = raw21783step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21783step0 raw21783step0Labels permutation38 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw21784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21784step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21784 raw21784Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw21784 raw21784Labels = mixedMoment B raw21784step0 raw21784step0Labels := by
      have hz : ∀ j, raw21784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21784step0 = (fun i j => raw21784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21784step0 raw21784; decide +kernel
      have hl : raw21784step0Labels = raw21784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21784 raw21784Labels permutation434 hz
    mixedMoment B raw21784step0 raw21784step0Labels = mixedMoment B raw21784step1 raw21784step1Labels := by
      have hz : ∀ j, raw21784step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21784step1 = (fun i j => raw21784step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21784step1 raw21784step0; decide +kernel
      have hl : raw21784step1Labels = raw21784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21784step0 raw21784step0Labels permutation56 hz
    mixedMoment B raw21784step1 raw21784step1Labels = mixedMoment B raw21784step2 raw21784step2Labels := by
      have ha : raw21784step2 = (fun i j => raw21784step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21784step2 raw21784step1; decide +kernel
      have hl : raw21784step2Labels = raw21784step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21784step1 raw21784step1Labels permutation10 permutation2
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw21785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21785 raw21785Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw21785 raw21785Labels = mixedMoment B raw21785step0 raw21785step0Labels := by
      have hz : ∀ j, raw21785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21785step0 = (fun i j => raw21785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21785step0 raw21785; decide +kernel
      have hl : raw21785step0Labels = raw21785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21785 raw21785Labels permutation434 hz
    mixedMoment B raw21785step0 raw21785step0Labels = mixedMoment B raw21785step1 raw21785step1Labels := by
      have hz : ∀ j, raw21785step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21785step1 = (fun i j => raw21785step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21785step1 raw21785step0; decide +kernel
      have hl : raw21785step1Labels = raw21785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21785step0 raw21785step0Labels permutation56 hz
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw21786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21786 raw21786Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw21786 raw21786Labels = mixedMoment B raw21786step0 raw21786step0Labels := by
      have hz : ∀ j, raw21786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21786step0 = (fun i j => raw21786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21786step0 raw21786; decide +kernel
      have hl : raw21786step0Labels = raw21786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21786 raw21786Labels permutation346 hz
    mixedMoment B raw21786step0 raw21786step0Labels = mixedMoment B raw21786step1 raw21786step1Labels := by
      have hz : ∀ j, raw21786step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21786step1 = (fun i j => raw21786step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21786step1 raw21786step0; decide +kernel
      have hl : raw21786step1Labels = raw21786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21786step0 raw21786step0Labels permutation56 hz
    _ = mixedMoment B node4177 node4177Labels := by rfl

def raw21787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21787 raw21787Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21787 raw21787Labels = mixedMoment B raw21787step0 raw21787step0Labels := by
      have hz : ∀ j, raw21787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21787step0 = (fun i j => raw21787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21787step0 raw21787; decide +kernel
      have hl : raw21787step0Labels = raw21787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21787 raw21787Labels permutation346 hz
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw21788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21788 raw21788Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21788 raw21788Labels = mixedMoment B raw21788step0 raw21788step0Labels := by
      have hz : ∀ j, raw21788 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21788step0 = (fun i j => raw21788 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21788step0 raw21788; decide +kernel
      have hl : raw21788step0Labels = raw21788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21788 raw21788Labels permutation265 hz
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw21789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21789 raw21789Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw21789 raw21789Labels = mixedMoment B raw21789step0 raw21789step0Labels := by
      have hz : ∀ j, raw21789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21789step0 = (fun i j => raw21789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21789step0 raw21789; decide +kernel
      have hl : raw21789step0Labels = raw21789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21789 raw21789Labels permutation346 hz
    mixedMoment B raw21789step0 raw21789step0Labels = mixedMoment B raw21789step1 raw21789step1Labels := by
      have hz : ∀ j, raw21789step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21789step1 = (fun i j => raw21789step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21789step1 raw21789step0; decide +kernel
      have hl : raw21789step1Labels = raw21789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21789step0 raw21789step0Labels permutation56 hz
    mixedMoment B raw21789step1 raw21789step1Labels = mixedMoment B raw21789step2 raw21789step2Labels := by
      have ha : raw21789step2 = (fun i j => raw21789step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21789step2 raw21789step1; decide +kernel
      have hl : raw21789step2Labels = raw21789step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21789step1 raw21789step1Labels permutation10 permutation2
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw21790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21790 raw21790Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw21790 raw21790Labels = mixedMoment B raw21790step0 raw21790step0Labels := by
      have hz : ∀ j, raw21790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21790step0 = (fun i j => raw21790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21790step0 raw21790; decide +kernel
      have hl : raw21790step0Labels = raw21790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21790 raw21790Labels permutation346 hz
    mixedMoment B raw21790step0 raw21790step0Labels = mixedMoment B raw21790step1 raw21790step1Labels := by
      have hz : ∀ j, raw21790step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21790step1 = (fun i j => raw21790step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21790step1 raw21790step0; decide +kernel
      have hl : raw21790step1Labels = raw21790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21790step0 raw21790step0Labels permutation56 hz
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw21791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21791step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw21791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21791 raw21791Labels = mixedMoment B node4191 node4191Labels := by
  calc
    mixedMoment B raw21791 raw21791Labels = mixedMoment B raw21791step0 raw21791step0Labels := by
      have hz : ∀ j, raw21791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21791step0 = (fun i j => raw21791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21791step0 raw21791; decide +kernel
      have hl : raw21791step0Labels = raw21791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21791 raw21791Labels permutation434 hz
    mixedMoment B raw21791step0 raw21791step0Labels = mixedMoment B raw21791step1 raw21791step1Labels := by
      have hz : ∀ j, raw21791step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21791step1 = (fun i j => raw21791step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21791step1 raw21791step0; decide +kernel
      have hl : raw21791step1Labels = raw21791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21791step0 raw21791step0Labels permutation80 hz
    mixedMoment B raw21791step1 raw21791step1Labels = mixedMoment B raw21791step2 raw21791step2Labels := by
      have hz : ∀ j, raw21791step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21791step2 = (fun i j => raw21791step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21791step2 raw21791step1; decide +kernel
      have hl : raw21791step2Labels = raw21791step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21791step1 raw21791step1Labels permutation14 hz
    _ = mixedMoment B node4191 node4191Labels := by rfl

def raw21792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21792 raw21792Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw21792 raw21792Labels = mixedMoment B raw21792step0 raw21792step0Labels := by
      have hz : ∀ j, raw21792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21792step0 = (fun i j => raw21792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21792step0 raw21792; decide +kernel
      have hl : raw21792step0Labels = raw21792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21792 raw21792Labels permutation434 hz
    mixedMoment B raw21792step0 raw21792step0Labels = mixedMoment B raw21792step1 raw21792step1Labels := by
      have hz : ∀ j, raw21792step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21792step1 = (fun i j => raw21792step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21792step1 raw21792step0; decide +kernel
      have hl : raw21792step1Labels = raw21792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21792step0 raw21792step0Labels permutation80 hz
    _ = mixedMoment B node4360 node4360Labels := by rfl

def raw21793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21793 raw21793Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw21793 raw21793Labels = mixedMoment B raw21793step0 raw21793step0Labels := by
      have hz : ∀ j, raw21793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21793step0 = (fun i j => raw21793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21793step0 raw21793; decide +kernel
      have hl : raw21793step0Labels = raw21793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21793 raw21793Labels permutation434 hz
    mixedMoment B raw21793step0 raw21793step0Labels = mixedMoment B raw21793step1 raw21793step1Labels := by
      have hz : ∀ j, raw21793step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21793step1 = (fun i j => raw21793step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21793step1 raw21793step0; decide +kernel
      have hl : raw21793step1Labels = raw21793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21793step0 raw21793step0Labels permutation56 hz
    _ = mixedMoment B node4360 node4360Labels := by rfl

def raw21794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21794 raw21794Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw21794 raw21794Labels = mixedMoment B raw21794step0 raw21794step0Labels := by
      have hz : ∀ j, raw21794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21794step0 = (fun i j => raw21794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21794step0 raw21794; decide +kernel
      have hl : raw21794step0Labels = raw21794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21794 raw21794Labels permutation346 hz
    mixedMoment B raw21794step0 raw21794step0Labels = mixedMoment B raw21794step1 raw21794step1Labels := by
      have hz : ∀ j, raw21794step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21794step1 = (fun i j => raw21794step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21794step1 raw21794step0; decide +kernel
      have hl : raw21794step1Labels = raw21794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21794step0 raw21794step0Labels permutation56 hz
    _ = mixedMoment B node4360 node4360Labels := by rfl

def raw21795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21795step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw21795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21795 raw21795Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw21795 raw21795Labels = mixedMoment B raw21795step0 raw21795step0Labels := by
      have hz : ∀ j, raw21795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21795step0 = (fun i j => raw21795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21795step0 raw21795; decide +kernel
      have hl : raw21795step0Labels = raw21795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21795 raw21795Labels permutation434 hz
    mixedMoment B raw21795step0 raw21795step0Labels = mixedMoment B raw21795step1 raw21795step1Labels := by
      have hz : ∀ j, raw21795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21795step1 = (fun i j => raw21795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21795step1 raw21795step0; decide +kernel
      have hl : raw21795step1Labels = raw21795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21795step0 raw21795step0Labels permutation80 hz
    mixedMoment B raw21795step1 raw21795step1Labels = mixedMoment B raw21795step2 raw21795step2Labels := by
      have hz : ∀ j, raw21795step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21795step2 = (fun i j => raw21795step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21795step2 raw21795step1; decide +kernel
      have hl : raw21795step2Labels = raw21795step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21795step1 raw21795step1Labels permutation14 hz
    _ = mixedMoment B node4511 node4511Labels := by rfl

def raw21796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21796step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw21796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21796 raw21796Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw21796 raw21796Labels = mixedMoment B raw21796step0 raw21796step0Labels := by
      have hz : ∀ j, raw21796 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21796step0 = (fun i j => raw21796 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21796step0 raw21796; decide +kernel
      have hl : raw21796step0Labels = raw21796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21796 raw21796Labels permutation434 hz
    mixedMoment B raw21796step0 raw21796step0Labels = mixedMoment B raw21796step1 raw21796step1Labels := by
      have hz : ∀ j, raw21796step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21796step1 = (fun i j => raw21796step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21796step1 raw21796step0; decide +kernel
      have hl : raw21796step1Labels = raw21796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21796step0 raw21796step0Labels permutation80 hz
    mixedMoment B raw21796step1 raw21796step1Labels = mixedMoment B raw21796step2 raw21796step2Labels := by
      have hz : ∀ j, raw21796step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21796step2 = (fun i j => raw21796step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21796step2 raw21796step1; decide +kernel
      have hl : raw21796step2Labels = raw21796step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21796step1 raw21796step1Labels permutation14 hz
    _ = mixedMoment B node4187 node4187Labels := by rfl

def raw21797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21797 raw21797Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw21797 raw21797Labels = mixedMoment B raw21797step0 raw21797step0Labels := by
      have hz : ∀ j, raw21797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21797step0 = (fun i j => raw21797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21797step0 raw21797; decide +kernel
      have hl : raw21797step0Labels = raw21797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21797 raw21797Labels permutation434 hz
    mixedMoment B raw21797step0 raw21797step0Labels = mixedMoment B raw21797step1 raw21797step1Labels := by
      have hz : ∀ j, raw21797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21797step1 = (fun i j => raw21797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21797step1 raw21797step0; decide +kernel
      have hl : raw21797step1Labels = raw21797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21797step0 raw21797step0Labels permutation80 hz
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw21798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21798 raw21798Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw21798 raw21798Labels = mixedMoment B raw21798step0 raw21798step0Labels := by
      have hz : ∀ j, raw21798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21798step0 = (fun i j => raw21798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21798step0 raw21798; decide +kernel
      have hl : raw21798step0Labels = raw21798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21798 raw21798Labels permutation434 hz
    mixedMoment B raw21798step0 raw21798step0Labels = mixedMoment B raw21798step1 raw21798step1Labels := by
      have hz : ∀ j, raw21798step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21798step1 = (fun i j => raw21798step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21798step1 raw21798step0; decide +kernel
      have hl : raw21798step1Labels = raw21798step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21798step0 raw21798step0Labels permutation56 hz
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw21799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21799 raw21799Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw21799 raw21799Labels = mixedMoment B raw21799step0 raw21799step0Labels := by
      have hz : ∀ j, raw21799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21799step0 = (fun i j => raw21799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21799step0 raw21799; decide +kernel
      have hl : raw21799step0Labels = raw21799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21799 raw21799Labels permutation346 hz
    mixedMoment B raw21799step0 raw21799step0Labels = mixedMoment B raw21799step1 raw21799step1Labels := by
      have hz : ∀ j, raw21799step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21799step1 = (fun i j => raw21799step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21799step1 raw21799step0; decide +kernel
      have hl : raw21799step1Labels = raw21799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21799step0 raw21799step0Labels permutation56 hz
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw21800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21800step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21800step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21800 raw21800Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw21800 raw21800Labels = mixedMoment B raw21800step0 raw21800step0Labels := by
      have hz : ∀ j, raw21800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21800step0 = (fun i j => raw21800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21800step0 raw21800; decide +kernel
      have hl : raw21800step0Labels = raw21800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21800 raw21800Labels permutation434 hz
    mixedMoment B raw21800step0 raw21800step0Labels = mixedMoment B raw21800step1 raw21800step1Labels := by
      have hz : ∀ j, raw21800step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21800step1 = (fun i j => raw21800step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21800step1 raw21800step0; decide +kernel
      have hl : raw21800step1Labels = raw21800step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21800step0 raw21800step0Labels permutation80 hz
    mixedMoment B raw21800step1 raw21800step1Labels = mixedMoment B raw21800step2 raw21800step2Labels := by
      have hz : ∀ j, raw21800step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21800step2 = (fun i j => raw21800step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21800step2 raw21800step1; decide +kernel
      have hl : raw21800step2Labels = raw21800step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21800step1 raw21800step1Labels permutation14 hz
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw21801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21801step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21801step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21801step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21801step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21801step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21801step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21801 raw21801Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw21801 raw21801Labels = mixedMoment B raw21801step0 raw21801step0Labels := by
      have hz : ∀ j, raw21801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21801step0 = (fun i j => raw21801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21801step0 raw21801; decide +kernel
      have hl : raw21801step0Labels = raw21801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21801 raw21801Labels permutation434 hz
    mixedMoment B raw21801step0 raw21801step0Labels = mixedMoment B raw21801step1 raw21801step1Labels := by
      have hz : ∀ j, raw21801step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21801step1 = (fun i j => raw21801step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21801step1 raw21801step0; decide +kernel
      have hl : raw21801step1Labels = raw21801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21801step0 raw21801step0Labels permutation80 hz
    mixedMoment B raw21801step1 raw21801step1Labels = mixedMoment B raw21801step2 raw21801step2Labels := by
      have ha : raw21801step2 = (fun i j => raw21801step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21801step2 raw21801step1; decide +kernel
      have hl : raw21801step2Labels = raw21801step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21801step1 raw21801step1Labels permutation8 permutation7
    mixedMoment B raw21801step2 raw21801step2Labels = mixedMoment B raw21801step3 raw21801step3Labels := by
      have ha : raw21801step3 = -raw21801step2 := by apply Matrix.ext; change ∀ i j, raw21801step3 i j = -(raw21801step2 i j); unfold raw21801step3 raw21801step2; decide +kernel
      have hl : raw21801step3Labels = raw21801step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21801step3 raw21801step3Labels = mixedMoment B raw21801step4 raw21801step4Labels := by
      have ha : raw21801step4 = raw21801step3 := by apply Matrix.ext; unfold raw21801step4 raw21801step3; decide +kernel
      have hl : raw21801step3Labels = labelEmbedding1 ∘ raw21801step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21801step3 raw21801step3Labels raw21801step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw21802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21802step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21802step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21802step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21802step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21802step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21802 raw21802Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw21802 raw21802Labels = mixedMoment B raw21802step0 raw21802step0Labels := by
      have hz : ∀ j, raw21802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21802step0 = (fun i j => raw21802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21802step0 raw21802; decide +kernel
      have hl : raw21802step0Labels = raw21802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21802 raw21802Labels permutation434 hz
    mixedMoment B raw21802step0 raw21802step0Labels = mixedMoment B raw21802step1 raw21802step1Labels := by
      have hz : ∀ j, raw21802step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21802step1 = (fun i j => raw21802step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21802step1 raw21802step0; decide +kernel
      have hl : raw21802step1Labels = raw21802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21802step0 raw21802step0Labels permutation56 hz
    mixedMoment B raw21802step1 raw21802step1Labels = mixedMoment B raw21802step2 raw21802step2Labels := by
      have ha : raw21802step2 = (fun i j => raw21802step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21802step2 raw21802step1; decide +kernel
      have hl : raw21802step2Labels = raw21802step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21802step1 raw21802step1Labels permutation8 permutation7
    mixedMoment B raw21802step2 raw21802step2Labels = mixedMoment B raw21802step3 raw21802step3Labels := by
      have ha : raw21802step3 = -raw21802step2 := by apply Matrix.ext; change ∀ i j, raw21802step3 i j = -(raw21802step2 i j); unfold raw21802step3 raw21802step2; decide +kernel
      have hl : raw21802step3Labels = raw21802step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21802step3 raw21802step3Labels = mixedMoment B raw21802step4 raw21802step4Labels := by
      have ha : raw21802step4 = raw21802step3 := by apply Matrix.ext; unfold raw21802step4 raw21802step3; decide +kernel
      have hl : raw21802step3Labels = labelEmbedding1 ∘ raw21802step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21802step3 raw21802step3Labels raw21802step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw21803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21803step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21803step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21803step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21803step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21803step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21803 raw21803Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw21803 raw21803Labels = mixedMoment B raw21803step0 raw21803step0Labels := by
      have hz : ∀ j, raw21803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21803step0 = (fun i j => raw21803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21803step0 raw21803; decide +kernel
      have hl : raw21803step0Labels = raw21803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21803 raw21803Labels permutation346 hz
    mixedMoment B raw21803step0 raw21803step0Labels = mixedMoment B raw21803step1 raw21803step1Labels := by
      have hz : ∀ j, raw21803step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21803step1 = (fun i j => raw21803step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21803step1 raw21803step0; decide +kernel
      have hl : raw21803step1Labels = raw21803step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21803step0 raw21803step0Labels permutation56 hz
    mixedMoment B raw21803step1 raw21803step1Labels = mixedMoment B raw21803step2 raw21803step2Labels := by
      have ha : raw21803step2 = (fun i j => raw21803step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21803step2 raw21803step1; decide +kernel
      have hl : raw21803step2Labels = raw21803step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21803step1 raw21803step1Labels permutation8 permutation7
    mixedMoment B raw21803step2 raw21803step2Labels = mixedMoment B raw21803step3 raw21803step3Labels := by
      have ha : raw21803step3 = -raw21803step2 := by apply Matrix.ext; change ∀ i j, raw21803step3 i j = -(raw21803step2 i j); unfold raw21803step3 raw21803step2; decide +kernel
      have hl : raw21803step3Labels = raw21803step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21803step3 raw21803step3Labels = mixedMoment B raw21803step4 raw21803step4Labels := by
      have ha : raw21803step4 = raw21803step3 := by apply Matrix.ext; unfold raw21803step4 raw21803step3; decide +kernel
      have hl : raw21803step3Labels = labelEmbedding1 ∘ raw21803step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21803step3 raw21803step3Labels raw21803step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw21804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21804step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21804step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21804step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-2, -1, 3]]
def raw21804step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21804step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21804step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21804step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21804step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21804 raw21804Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw21804 raw21804Labels = mixedMoment B raw21804step0 raw21804step0Labels := by
      have hz : ∀ j, raw21804 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21804step0 = (fun i j => raw21804 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21804step0 raw21804; decide +kernel
      have hl : raw21804step0Labels = raw21804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21804 raw21804Labels permutation434 hz
    mixedMoment B raw21804step0 raw21804step0Labels = mixedMoment B raw21804step1 raw21804step1Labels := by
      have hz : ∀ j, raw21804step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21804step1 = (fun i j => raw21804step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21804step1 raw21804step0; decide +kernel
      have hl : raw21804step1Labels = raw21804step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21804step0 raw21804step0Labels permutation80 hz
    mixedMoment B raw21804step1 raw21804step1Labels = mixedMoment B raw21804step2 raw21804step2Labels := by
      have hz : ∀ j, raw21804step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21804step2 = (fun i j => raw21804step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21804step2 raw21804step1; decide +kernel
      have hl : raw21804step2Labels = raw21804step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21804step1 raw21804step1Labels permutation14 hz
    mixedMoment B raw21804step2 raw21804step2Labels = mixedMoment B raw21804step3 raw21804step3Labels := by
      have ha : raw21804step3 = (fun i j => raw21804step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21804step3 raw21804step2; decide +kernel
      have hl : raw21804step3Labels = raw21804step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21804step2 raw21804step2Labels permutation2 permutation7
    mixedMoment B raw21804step3 raw21804step3Labels = mixedMoment B raw21804step4 raw21804step4Labels := by
      have ha : raw21804step4 = -raw21804step3 := by apply Matrix.ext; change ∀ i j, raw21804step4 i j = -(raw21804step3 i j); unfold raw21804step4 raw21804step3; decide +kernel
      have hl : raw21804step4Labels = raw21804step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21804step4 raw21804step4Labels = mixedMoment B raw21804step5 raw21804step5Labels := by
      have ha : raw21804step5 = raw21804step4 := by apply Matrix.ext; unfold raw21804step5 raw21804step4; decide +kernel
      have hl : raw21804step4Labels = labelEmbedding1 ∘ raw21804step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21804step4 raw21804step4Labels raw21804step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

def raw21805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21805step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![2, 0, -2]]
def raw21805step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21805step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw21805step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21805 raw21805Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw21805 raw21805Labels = mixedMoment B raw21805step0 raw21805step0Labels := by
      have hz : ∀ j, raw21805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21805step0 = (fun i j => raw21805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21805step0 raw21805; decide +kernel
      have hl : raw21805step0Labels = raw21805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21805 raw21805Labels permutation434 hz
    mixedMoment B raw21805step0 raw21805step0Labels = mixedMoment B raw21805step1 raw21805step1Labels := by
      have hz : ∀ j, raw21805step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21805step1 = (fun i j => raw21805step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21805step1 raw21805step0; decide +kernel
      have hl : raw21805step1Labels = raw21805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21805step0 raw21805step0Labels permutation80 hz
    mixedMoment B raw21805step1 raw21805step1Labels = mixedMoment B raw21805step2 raw21805step2Labels := by
      have hz : ∀ j, raw21805step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21805step2 = (fun i j => raw21805step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21805step2 raw21805step1; decide +kernel
      have hl : raw21805step2Labels = raw21805step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21805step1 raw21805step1Labels permutation14 hz
    mixedMoment B raw21805step2 raw21805step2Labels = mixedMoment B raw21805step3 raw21805step3Labels := by
      have hz : ∀ i, raw21805step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw21805step3 = (fun i j => raw21805step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw21805step3 raw21805step2; decide +kernel
      have hl : raw21805step3Labels = (fun j => raw21805step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw21805step2 raw21805step2Labels permutation4 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw21806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21806step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21806step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21806step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21806step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21806step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21806 raw21806Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw21806 raw21806Labels = mixedMoment B raw21806step0 raw21806step0Labels := by
      have hz : ∀ j, raw21806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21806step0 = (fun i j => raw21806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21806step0 raw21806; decide +kernel
      have hl : raw21806step0Labels = raw21806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21806 raw21806Labels permutation434 hz
    mixedMoment B raw21806step0 raw21806step0Labels = mixedMoment B raw21806step1 raw21806step1Labels := by
      have hz : ∀ j, raw21806step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21806step1 = (fun i j => raw21806step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21806step1 raw21806step0; decide +kernel
      have hl : raw21806step1Labels = raw21806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21806step0 raw21806step0Labels permutation80 hz
    mixedMoment B raw21806step1 raw21806step1Labels = mixedMoment B raw21806step2 raw21806step2Labels := by
      have ha : raw21806step2 = (fun i j => raw21806step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21806step2 raw21806step1; decide +kernel
      have hl : raw21806step2Labels = raw21806step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21806step1 raw21806step1Labels permutation8 permutation7
    mixedMoment B raw21806step2 raw21806step2Labels = mixedMoment B raw21806step3 raw21806step3Labels := by
      have ha : raw21806step3 = -raw21806step2 := by apply Matrix.ext; change ∀ i j, raw21806step3 i j = -(raw21806step2 i j); unfold raw21806step3 raw21806step2; decide +kernel
      have hl : raw21806step3Labels = raw21806step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21806step3 raw21806step3Labels = mixedMoment B raw21806step4 raw21806step4Labels := by
      have ha : raw21806step4 = raw21806step3 := by apply Matrix.ext; unfold raw21806step4 raw21806step3; decide +kernel
      have hl : raw21806step3Labels = labelEmbedding1 ∘ raw21806step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21806step3 raw21806step3Labels raw21806step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

def raw21807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21807step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21807step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21807step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21807step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21807 raw21807Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21807 raw21807Labels = mixedMoment B raw21807step0 raw21807step0Labels := by
      have hz : ∀ j, raw21807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21807step0 = (fun i j => raw21807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21807step0 raw21807; decide +kernel
      have hl : raw21807step0Labels = raw21807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21807 raw21807Labels permutation434 hz
    mixedMoment B raw21807step0 raw21807step0Labels = mixedMoment B raw21807step1 raw21807step1Labels := by
      have ha : raw21807step1 = (fun i j => raw21807step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21807step1 raw21807step0; decide +kernel
      have hl : raw21807step1Labels = raw21807step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21807step0 raw21807step0Labels permutation38 permutation7
    mixedMoment B raw21807step1 raw21807step1Labels = mixedMoment B raw21807step2 raw21807step2Labels := by
      have ha : raw21807step2 = -raw21807step1 := by apply Matrix.ext; change ∀ i j, raw21807step2 i j = -(raw21807step1 i j); unfold raw21807step2 raw21807step1; decide +kernel
      have hl : raw21807step2Labels = raw21807step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21807step2 raw21807step2Labels = mixedMoment B raw21807step3 raw21807step3Labels := by
      have ha : raw21807step3 = raw21807step2 := by apply Matrix.ext; unfold raw21807step3 raw21807step2; decide +kernel
      have hl : raw21807step2Labels = labelEmbedding1 ∘ raw21807step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21807step2 raw21807step2Labels raw21807step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw21808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21808 raw21808Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21808 raw21808Labels = mixedMoment B raw21808step0 raw21808step0Labels := by
      have hz : ∀ j, raw21808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21808step0 = (fun i j => raw21808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21808step0 raw21808; decide +kernel
      have hl : raw21808step0Labels = raw21808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21808 raw21808Labels permutation346 hz
    mixedMoment B raw21808step0 raw21808step0Labels = mixedMoment B raw21808step1 raw21808step1Labels := by
      have ha : raw21808step1 = (fun i j => raw21808step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21808step1 raw21808step0; decide +kernel
      have hl : raw21808step1Labels = raw21808step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21808step0 raw21808step0Labels permutation38 permutation7
    mixedMoment B raw21808step1 raw21808step1Labels = mixedMoment B raw21808step2 raw21808step2Labels := by
      have ha : raw21808step2 = -raw21808step1 := by apply Matrix.ext; change ∀ i j, raw21808step2 i j = -(raw21808step1 i j); unfold raw21808step2 raw21808step1; decide +kernel
      have hl : raw21808step2Labels = raw21808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21808step2 raw21808step2Labels = mixedMoment B raw21808step3 raw21808step3Labels := by
      have ha : raw21808step3 = raw21808step2 := by apply Matrix.ext; unfold raw21808step3 raw21808step2; decide +kernel
      have hl : raw21808step2Labels = labelEmbedding1 ∘ raw21808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21808step2 raw21808step2Labels raw21808step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw21809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21809step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21809step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21809step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21809step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21809step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21809 raw21809Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw21809 raw21809Labels = mixedMoment B raw21809step0 raw21809step0Labels := by
      have hz : ∀ j, raw21809 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21809step0 = (fun i j => raw21809 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21809step0 raw21809; decide +kernel
      have hl : raw21809step0Labels = raw21809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21809 raw21809Labels permutation434 hz
    mixedMoment B raw21809step0 raw21809step0Labels = mixedMoment B raw21809step1 raw21809step1Labels := by
      have hz : ∀ j, raw21809step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21809step1 = (fun i j => raw21809step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21809step1 raw21809step0; decide +kernel
      have hl : raw21809step1Labels = raw21809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21809step0 raw21809step0Labels permutation80 hz
    mixedMoment B raw21809step1 raw21809step1Labels = mixedMoment B raw21809step2 raw21809step2Labels := by
      have ha : raw21809step2 = (fun i j => raw21809step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21809step2 raw21809step1; decide +kernel
      have hl : raw21809step2Labels = raw21809step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21809step1 raw21809step1Labels permutation8 permutation7
    mixedMoment B raw21809step2 raw21809step2Labels = mixedMoment B raw21809step3 raw21809step3Labels := by
      have ha : raw21809step3 = -raw21809step2 := by apply Matrix.ext; change ∀ i j, raw21809step3 i j = -(raw21809step2 i j); unfold raw21809step3 raw21809step2; decide +kernel
      have hl : raw21809step3Labels = raw21809step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21809step3 raw21809step3Labels = mixedMoment B raw21809step4 raw21809step4Labels := by
      have ha : raw21809step4 = raw21809step3 := by apply Matrix.ext; unfold raw21809step4 raw21809step3; decide +kernel
      have hl : raw21809step3Labels = labelEmbedding1 ∘ raw21809step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21809step3 raw21809step3Labels raw21809step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw21810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21810step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21810step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw21810step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21810step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21810step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21810step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21810 raw21810Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw21810 raw21810Labels = mixedMoment B raw21810step0 raw21810step0Labels := by
      have hz : ∀ j, raw21810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21810step0 = (fun i j => raw21810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21810step0 raw21810; decide +kernel
      have hl : raw21810step0Labels = raw21810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21810 raw21810Labels permutation434 hz
    mixedMoment B raw21810step0 raw21810step0Labels = mixedMoment B raw21810step1 raw21810step1Labels := by
      have hz : ∀ j, raw21810step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21810step1 = (fun i j => raw21810step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21810step1 raw21810step0; decide +kernel
      have hl : raw21810step1Labels = raw21810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21810step0 raw21810step0Labels permutation80 hz
    mixedMoment B raw21810step1 raw21810step1Labels = mixedMoment B raw21810step2 raw21810step2Labels := by
      have ha : raw21810step2 = (fun i j => raw21810step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21810step2 raw21810step1; decide +kernel
      have hl : raw21810step2Labels = raw21810step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21810step1 raw21810step1Labels permutation8 permutation7
    mixedMoment B raw21810step2 raw21810step2Labels = mixedMoment B raw21810step3 raw21810step3Labels := by
      have ha : raw21810step3 = -raw21810step2 := by apply Matrix.ext; change ∀ i j, raw21810step3 i j = -(raw21810step2 i j); unfold raw21810step3 raw21810step2; decide +kernel
      have hl : raw21810step3Labels = raw21810step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21810step3 raw21810step3Labels = mixedMoment B raw21810step4 raw21810step4Labels := by
      have ha : raw21810step4 = raw21810step3 := by apply Matrix.ext; unfold raw21810step4 raw21810step3; decide +kernel
      have hl : raw21810step3Labels = labelEmbedding1 ∘ raw21810step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21810step3 raw21810step3Labels raw21810step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw21811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21811step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21811step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21811step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21811step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21811step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21811step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21811step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21811step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21811 raw21811Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw21811 raw21811Labels = mixedMoment B raw21811step0 raw21811step0Labels := by
      have hz : ∀ j, raw21811 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21811step0 = (fun i j => raw21811 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21811step0 raw21811; decide +kernel
      have hl : raw21811step0Labels = raw21811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21811 raw21811Labels permutation434 hz
    mixedMoment B raw21811step0 raw21811step0Labels = mixedMoment B raw21811step1 raw21811step1Labels := by
      have hz : ∀ j, raw21811step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21811step1 = (fun i j => raw21811step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21811step1 raw21811step0; decide +kernel
      have hl : raw21811step1Labels = raw21811step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21811step0 raw21811step0Labels permutation56 hz
    mixedMoment B raw21811step1 raw21811step1Labels = mixedMoment B raw21811step2 raw21811step2Labels := by
      have ha : raw21811step2 = (fun i j => raw21811step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21811step2 raw21811step1; decide +kernel
      have hl : raw21811step2Labels = raw21811step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21811step1 raw21811step1Labels permutation8 permutation7
    mixedMoment B raw21811step2 raw21811step2Labels = mixedMoment B raw21811step3 raw21811step3Labels := by
      have ha : raw21811step3 = -raw21811step2 := by apply Matrix.ext; change ∀ i j, raw21811step3 i j = -(raw21811step2 i j); unfold raw21811step3 raw21811step2; decide +kernel
      have hl : raw21811step3Labels = raw21811step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21811step3 raw21811step3Labels = mixedMoment B raw21811step4 raw21811step4Labels := by
      have ha : raw21811step4 = raw21811step3 := by apply Matrix.ext; unfold raw21811step4 raw21811step3; decide +kernel
      have hl : raw21811step3Labels = labelEmbedding1 ∘ raw21811step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21811step3 raw21811step3Labels raw21811step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

def raw21812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21812step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21812step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21812step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21812step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21812 raw21812Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21812 raw21812Labels = mixedMoment B raw21812step0 raw21812step0Labels := by
      have hz : ∀ j, raw21812 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21812step0 = (fun i j => raw21812 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21812step0 raw21812; decide +kernel
      have hl : raw21812step0Labels = raw21812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21812 raw21812Labels permutation434 hz
    mixedMoment B raw21812step0 raw21812step0Labels = mixedMoment B raw21812step1 raw21812step1Labels := by
      have ha : raw21812step1 = (fun i j => raw21812step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21812step1 raw21812step0; decide +kernel
      have hl : raw21812step1Labels = raw21812step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21812step0 raw21812step0Labels permutation32 permutation7
    mixedMoment B raw21812step1 raw21812step1Labels = mixedMoment B raw21812step2 raw21812step2Labels := by
      have ha : raw21812step2 = -raw21812step1 := by apply Matrix.ext; change ∀ i j, raw21812step2 i j = -(raw21812step1 i j); unfold raw21812step2 raw21812step1; decide +kernel
      have hl : raw21812step2Labels = raw21812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21812step2 raw21812step2Labels = mixedMoment B raw21812step3 raw21812step3Labels := by
      have ha : raw21812step3 = raw21812step2 := by apply Matrix.ext; unfold raw21812step3 raw21812step2; decide +kernel
      have hl : raw21812step2Labels = labelEmbedding1 ∘ raw21812step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21812step2 raw21812step2Labels raw21812step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw21813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21813step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21813step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21813 raw21813Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21813 raw21813Labels = mixedMoment B raw21813step0 raw21813step0Labels := by
      have hz : ∀ j, raw21813 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21813step0 = (fun i j => raw21813 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21813step0 raw21813; decide +kernel
      have hl : raw21813step0Labels = raw21813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21813 raw21813Labels permutation265 hz
    mixedMoment B raw21813step0 raw21813step0Labels = mixedMoment B raw21813step1 raw21813step1Labels := by
      have ha : raw21813step1 = (fun i j => raw21813step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21813step1 raw21813step0; decide +kernel
      have hl : raw21813step1Labels = raw21813step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21813step0 raw21813step0Labels permutation38 permutation7
    mixedMoment B raw21813step1 raw21813step1Labels = mixedMoment B raw21813step2 raw21813step2Labels := by
      have ha : raw21813step2 = -raw21813step1 := by apply Matrix.ext; change ∀ i j, raw21813step2 i j = -(raw21813step1 i j); unfold raw21813step2 raw21813step1; decide +kernel
      have hl : raw21813step2Labels = raw21813step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21813step2 raw21813step2Labels = mixedMoment B raw21813step3 raw21813step3Labels := by
      have ha : raw21813step3 = raw21813step2 := by apply Matrix.ext; unfold raw21813step3 raw21813step2; decide +kernel
      have hl : raw21813step2Labels = labelEmbedding1 ∘ raw21813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21813step2 raw21813step2Labels raw21813step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw21814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21814step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21814step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21814step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21814step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21814step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21814 raw21814Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw21814 raw21814Labels = mixedMoment B raw21814step0 raw21814step0Labels := by
      have hz : ∀ j, raw21814 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21814step0 = (fun i j => raw21814 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21814step0 raw21814; decide +kernel
      have hl : raw21814step0Labels = raw21814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21814 raw21814Labels permutation434 hz
    mixedMoment B raw21814step0 raw21814step0Labels = mixedMoment B raw21814step1 raw21814step1Labels := by
      have hz : ∀ j, raw21814step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21814step1 = (fun i j => raw21814step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21814step1 raw21814step0; decide +kernel
      have hl : raw21814step1Labels = raw21814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21814step0 raw21814step0Labels permutation56 hz
    mixedMoment B raw21814step1 raw21814step1Labels = mixedMoment B raw21814step2 raw21814step2Labels := by
      have ha : raw21814step2 = (fun i j => raw21814step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21814step2 raw21814step1; decide +kernel
      have hl : raw21814step2Labels = raw21814step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21814step1 raw21814step1Labels permutation8 permutation7
    mixedMoment B raw21814step2 raw21814step2Labels = mixedMoment B raw21814step3 raw21814step3Labels := by
      have ha : raw21814step3 = -raw21814step2 := by apply Matrix.ext; change ∀ i j, raw21814step3 i j = -(raw21814step2 i j); unfold raw21814step3 raw21814step2; decide +kernel
      have hl : raw21814step3Labels = raw21814step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21814step3 raw21814step3Labels = mixedMoment B raw21814step4 raw21814step4Labels := by
      have ha : raw21814step4 = raw21814step3 := by apply Matrix.ext; unfold raw21814step4 raw21814step3; decide +kernel
      have hl : raw21814step3Labels = labelEmbedding1 ∘ raw21814step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21814step3 raw21814step3Labels raw21814step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw21815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21815step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw21815step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21815step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21815step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21815step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21815step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21815 raw21815Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw21815 raw21815Labels = mixedMoment B raw21815step0 raw21815step0Labels := by
      have hz : ∀ j, raw21815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21815step0 = (fun i j => raw21815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21815step0 raw21815; decide +kernel
      have hl : raw21815step0Labels = raw21815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21815 raw21815Labels permutation434 hz
    mixedMoment B raw21815step0 raw21815step0Labels = mixedMoment B raw21815step1 raw21815step1Labels := by
      have hz : ∀ j, raw21815step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21815step1 = (fun i j => raw21815step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21815step1 raw21815step0; decide +kernel
      have hl : raw21815step1Labels = raw21815step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21815step0 raw21815step0Labels permutation56 hz
    mixedMoment B raw21815step1 raw21815step1Labels = mixedMoment B raw21815step2 raw21815step2Labels := by
      have ha : raw21815step2 = (fun i j => raw21815step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21815step2 raw21815step1; decide +kernel
      have hl : raw21815step2Labels = raw21815step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21815step1 raw21815step1Labels permutation8 permutation7
    mixedMoment B raw21815step2 raw21815step2Labels = mixedMoment B raw21815step3 raw21815step3Labels := by
      have ha : raw21815step3 = -raw21815step2 := by apply Matrix.ext; change ∀ i j, raw21815step3 i j = -(raw21815step2 i j); unfold raw21815step3 raw21815step2; decide +kernel
      have hl : raw21815step3Labels = raw21815step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21815step3 raw21815step3Labels = mixedMoment B raw21815step4 raw21815step4Labels := by
      have ha : raw21815step4 = raw21815step3 := by apply Matrix.ext; unfold raw21815step4 raw21815step3; decide +kernel
      have hl : raw21815step3Labels = labelEmbedding1 ∘ raw21815step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21815step3 raw21815step3Labels raw21815step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw21816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21816step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21816step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21816step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21816step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21816step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21816step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21816step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21816step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21816 raw21816Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw21816 raw21816Labels = mixedMoment B raw21816step0 raw21816step0Labels := by
      have hz : ∀ j, raw21816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21816step0 = (fun i j => raw21816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21816step0 raw21816; decide +kernel
      have hl : raw21816step0Labels = raw21816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21816 raw21816Labels permutation346 hz
    mixedMoment B raw21816step0 raw21816step0Labels = mixedMoment B raw21816step1 raw21816step1Labels := by
      have hz : ∀ j, raw21816step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21816step1 = (fun i j => raw21816step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21816step1 raw21816step0; decide +kernel
      have hl : raw21816step1Labels = raw21816step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21816step0 raw21816step0Labels permutation56 hz
    mixedMoment B raw21816step1 raw21816step1Labels = mixedMoment B raw21816step2 raw21816step2Labels := by
      have ha : raw21816step2 = (fun i j => raw21816step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21816step2 raw21816step1; decide +kernel
      have hl : raw21816step2Labels = raw21816step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21816step1 raw21816step1Labels permutation8 permutation7
    mixedMoment B raw21816step2 raw21816step2Labels = mixedMoment B raw21816step3 raw21816step3Labels := by
      have ha : raw21816step3 = -raw21816step2 := by apply Matrix.ext; change ∀ i j, raw21816step3 i j = -(raw21816step2 i j); unfold raw21816step3 raw21816step2; decide +kernel
      have hl : raw21816step3Labels = raw21816step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21816step3 raw21816step3Labels = mixedMoment B raw21816step4 raw21816step4Labels := by
      have ha : raw21816step4 = raw21816step3 := by apply Matrix.ext; unfold raw21816step4 raw21816step3; decide +kernel
      have hl : raw21816step3Labels = labelEmbedding1 ∘ raw21816step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21816step3 raw21816step3Labels raw21816step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

def raw21817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21817step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21817step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21817step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21817step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21817 raw21817Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21817 raw21817Labels = mixedMoment B raw21817step0 raw21817step0Labels := by
      have hz : ∀ j, raw21817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21817step0 = (fun i j => raw21817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21817step0 raw21817; decide +kernel
      have hl : raw21817step0Labels = raw21817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21817 raw21817Labels permutation346 hz
    mixedMoment B raw21817step0 raw21817step0Labels = mixedMoment B raw21817step1 raw21817step1Labels := by
      have ha : raw21817step1 = (fun i j => raw21817step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21817step1 raw21817step0; decide +kernel
      have hl : raw21817step1Labels = raw21817step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21817step0 raw21817step0Labels permutation32 permutation7
    mixedMoment B raw21817step1 raw21817step1Labels = mixedMoment B raw21817step2 raw21817step2Labels := by
      have ha : raw21817step2 = -raw21817step1 := by apply Matrix.ext; change ∀ i j, raw21817step2 i j = -(raw21817step1 i j); unfold raw21817step2 raw21817step1; decide +kernel
      have hl : raw21817step2Labels = raw21817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21817step2 raw21817step2Labels = mixedMoment B raw21817step3 raw21817step3Labels := by
      have ha : raw21817step3 = raw21817step2 := by apply Matrix.ext; unfold raw21817step3 raw21817step2; decide +kernel
      have hl : raw21817step2Labels = labelEmbedding1 ∘ raw21817step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21817step2 raw21817step2Labels raw21817step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw21818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21818step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21818step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21818step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21818 raw21818Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21818 raw21818Labels = mixedMoment B raw21818step0 raw21818step0Labels := by
      have hz : ∀ j, raw21818 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21818step0 = (fun i j => raw21818 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21818step0 raw21818; decide +kernel
      have hl : raw21818step0Labels = raw21818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21818 raw21818Labels permutation265 hz
    mixedMoment B raw21818step0 raw21818step0Labels = mixedMoment B raw21818step1 raw21818step1Labels := by
      have ha : raw21818step1 = (fun i j => raw21818step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21818step1 raw21818step0; decide +kernel
      have hl : raw21818step1Labels = raw21818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21818step0 raw21818step0Labels permutation32 permutation7
    mixedMoment B raw21818step1 raw21818step1Labels = mixedMoment B raw21818step2 raw21818step2Labels := by
      have ha : raw21818step2 = -raw21818step1 := by apply Matrix.ext; change ∀ i j, raw21818step2 i j = -(raw21818step1 i j); unfold raw21818step2 raw21818step1; decide +kernel
      have hl : raw21818step2Labels = raw21818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21818step2 raw21818step2Labels = mixedMoment B raw21818step3 raw21818step3Labels := by
      have ha : raw21818step3 = raw21818step2 := by apply Matrix.ext; unfold raw21818step3 raw21818step2; decide +kernel
      have hl : raw21818step2Labels = labelEmbedding1 ∘ raw21818step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21818step2 raw21818step2Labels raw21818step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw21819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw21819step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21819step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21819step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21819step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21819step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21819step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21819step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21819 raw21819Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw21819 raw21819Labels = mixedMoment B raw21819step0 raw21819step0Labels := by
      have hz : ∀ j, raw21819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21819step0 = (fun i j => raw21819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21819step0 raw21819; decide +kernel
      have hl : raw21819step0Labels = raw21819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21819 raw21819Labels permutation346 hz
    mixedMoment B raw21819step0 raw21819step0Labels = mixedMoment B raw21819step1 raw21819step1Labels := by
      have hz : ∀ j, raw21819step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21819step1 = (fun i j => raw21819step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21819step1 raw21819step0; decide +kernel
      have hl : raw21819step1Labels = raw21819step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21819step0 raw21819step0Labels permutation56 hz
    mixedMoment B raw21819step1 raw21819step1Labels = mixedMoment B raw21819step2 raw21819step2Labels := by
      have ha : raw21819step2 = (fun i j => raw21819step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21819step2 raw21819step1; decide +kernel
      have hl : raw21819step2Labels = raw21819step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21819step1 raw21819step1Labels permutation8 permutation7
    mixedMoment B raw21819step2 raw21819step2Labels = mixedMoment B raw21819step3 raw21819step3Labels := by
      have ha : raw21819step3 = -raw21819step2 := by apply Matrix.ext; change ∀ i j, raw21819step3 i j = -(raw21819step2 i j); unfold raw21819step3 raw21819step2; decide +kernel
      have hl : raw21819step3Labels = raw21819step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21819step3 raw21819step3Labels = mixedMoment B raw21819step4 raw21819step4Labels := by
      have ha : raw21819step4 = raw21819step3 := by apply Matrix.ext; unfold raw21819step4 raw21819step3; decide +kernel
      have hl : raw21819step3Labels = labelEmbedding1 ∘ raw21819step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21819step3 raw21819step3Labels raw21819step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw21820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21820step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21820step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21820step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw21820step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21820step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21820step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21820step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21820step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21820 raw21820Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw21820 raw21820Labels = mixedMoment B raw21820step0 raw21820step0Labels := by
      have hz : ∀ j, raw21820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21820step0 = (fun i j => raw21820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21820step0 raw21820; decide +kernel
      have hl : raw21820step0Labels = raw21820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21820 raw21820Labels permutation346 hz
    mixedMoment B raw21820step0 raw21820step0Labels = mixedMoment B raw21820step1 raw21820step1Labels := by
      have hz : ∀ j, raw21820step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21820step1 = (fun i j => raw21820step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21820step1 raw21820step0; decide +kernel
      have hl : raw21820step1Labels = raw21820step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21820step0 raw21820step0Labels permutation56 hz
    mixedMoment B raw21820step1 raw21820step1Labels = mixedMoment B raw21820step2 raw21820step2Labels := by
      have ha : raw21820step2 = (fun i j => raw21820step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21820step2 raw21820step1; decide +kernel
      have hl : raw21820step2Labels = raw21820step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21820step1 raw21820step1Labels permutation8 permutation7
    mixedMoment B raw21820step2 raw21820step2Labels = mixedMoment B raw21820step3 raw21820step3Labels := by
      have ha : raw21820step3 = -raw21820step2 := by apply Matrix.ext; change ∀ i j, raw21820step3 i j = -(raw21820step2 i j); unfold raw21820step3 raw21820step2; decide +kernel
      have hl : raw21820step3Labels = raw21820step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21820step3 raw21820step3Labels = mixedMoment B raw21820step4 raw21820step4Labels := by
      have ha : raw21820step4 = raw21820step3 := by apply Matrix.ext; unfold raw21820step4 raw21820step3; decide +kernel
      have hl : raw21820step3Labels = labelEmbedding1 ∘ raw21820step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21820step3 raw21820step3Labels raw21820step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw21821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21821step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21821step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw21821step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21821step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw21821step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21821step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw21821step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21821step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw21821step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21821 raw21821Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw21821 raw21821Labels = mixedMoment B raw21821step0 raw21821step0Labels := by
      have hz : ∀ j, raw21821 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21821step0 = (fun i j => raw21821 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21821step0 raw21821; decide +kernel
      have hl : raw21821step0Labels = raw21821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21821 raw21821Labels permutation434 hz
    mixedMoment B raw21821step0 raw21821step0Labels = mixedMoment B raw21821step1 raw21821step1Labels := by
      have hz : ∀ j, raw21821step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21821step1 = (fun i j => raw21821step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21821step1 raw21821step0; decide +kernel
      have hl : raw21821step1Labels = raw21821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21821step0 raw21821step0Labels permutation80 hz
    mixedMoment B raw21821step1 raw21821step1Labels = mixedMoment B raw21821step2 raw21821step2Labels := by
      have hz : ∀ j, raw21821step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21821step2 = (fun i j => raw21821step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21821step2 raw21821step1; decide +kernel
      have hl : raw21821step2Labels = raw21821step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21821step1 raw21821step1Labels permutation14 hz
    mixedMoment B raw21821step2 raw21821step2Labels = mixedMoment B raw21821step3 raw21821step3Labels := by
      have ha : raw21821step3 = (fun i j => raw21821step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21821step3 raw21821step2; decide +kernel
      have hl : raw21821step3Labels = raw21821step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21821step2 raw21821step2Labels permutation2 permutation7
    mixedMoment B raw21821step3 raw21821step3Labels = mixedMoment B raw21821step4 raw21821step4Labels := by
      have ha : raw21821step4 = -raw21821step3 := by apply Matrix.ext; change ∀ i j, raw21821step4 i j = -(raw21821step3 i j); unfold raw21821step4 raw21821step3; decide +kernel
      have hl : raw21821step4Labels = raw21821step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21821step4 raw21821step4Labels = mixedMoment B raw21821step5 raw21821step5Labels := by
      have ha : raw21821step5 = raw21821step4 := by apply Matrix.ext; unfold raw21821step5 raw21821step4; decide +kernel
      have hl : raw21821step4Labels = labelEmbedding1 ∘ raw21821step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21821step4 raw21821step4Labels raw21821step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1538 node1538Labels := by rfl

def raw21822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21822step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21822step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21822step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21822step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw21822step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21822step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21822step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21822step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21822step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21822 raw21822Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw21822 raw21822Labels = mixedMoment B raw21822step0 raw21822step0Labels := by
      have hz : ∀ j, raw21822 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21822step0 = (fun i j => raw21822 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21822step0 raw21822; decide +kernel
      have hl : raw21822step0Labels = raw21822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21822 raw21822Labels permutation434 hz
    mixedMoment B raw21822step0 raw21822step0Labels = mixedMoment B raw21822step1 raw21822step1Labels := by
      have hz : ∀ j, raw21822step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21822step1 = (fun i j => raw21822step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21822step1 raw21822step0; decide +kernel
      have hl : raw21822step1Labels = raw21822step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21822step0 raw21822step0Labels permutation80 hz
    mixedMoment B raw21822step1 raw21822step1Labels = mixedMoment B raw21822step2 raw21822step2Labels := by
      have ha : raw21822step2 = (fun i j => raw21822step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21822step2 raw21822step1; decide +kernel
      have hl : raw21822step2Labels = raw21822step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21822step1 raw21822step1Labels permutation8 permutation7
    mixedMoment B raw21822step2 raw21822step2Labels = mixedMoment B raw21822step3 raw21822step3Labels := by
      have ha : raw21822step3 = -raw21822step2 := by apply Matrix.ext; change ∀ i j, raw21822step3 i j = -(raw21822step2 i j); unfold raw21822step3 raw21822step2; decide +kernel
      have hl : raw21822step3Labels = raw21822step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21822step3 raw21822step3Labels = mixedMoment B raw21822step4 raw21822step4Labels := by
      have ha : raw21822step4 = raw21822step3 := by apply Matrix.ext; unfold raw21822step4 raw21822step3; decide +kernel
      have hl : raw21822step3Labels = labelEmbedding1 ∘ raw21822step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21822step3 raw21822step3Labels raw21822step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

def raw21823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21823step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21823step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw21823step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21823step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21823step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21823step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21823step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21823 raw21823Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw21823 raw21823Labels = mixedMoment B raw21823step0 raw21823step0Labels := by
      have hz : ∀ j, raw21823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21823step0 = (fun i j => raw21823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21823step0 raw21823; decide +kernel
      have hl : raw21823step0Labels = raw21823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21823 raw21823Labels permutation434 hz
    mixedMoment B raw21823step0 raw21823step0Labels = mixedMoment B raw21823step1 raw21823step1Labels := by
      have hz : ∀ j, raw21823step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21823step1 = (fun i j => raw21823step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21823step1 raw21823step0; decide +kernel
      have hl : raw21823step1Labels = raw21823step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21823step0 raw21823step0Labels permutation56 hz
    mixedMoment B raw21823step1 raw21823step1Labels = mixedMoment B raw21823step2 raw21823step2Labels := by
      have ha : raw21823step2 = (fun i j => raw21823step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21823step2 raw21823step1; decide +kernel
      have hl : raw21823step2Labels = raw21823step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21823step1 raw21823step1Labels permutation8 permutation7
    mixedMoment B raw21823step2 raw21823step2Labels = mixedMoment B raw21823step3 raw21823step3Labels := by
      have ha : raw21823step3 = -raw21823step2 := by apply Matrix.ext; change ∀ i j, raw21823step3 i j = -(raw21823step2 i j); unfold raw21823step3 raw21823step2; decide +kernel
      have hl : raw21823step3Labels = raw21823step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21823step3 raw21823step3Labels = mixedMoment B raw21823step4 raw21823step4Labels := by
      have ha : raw21823step4 = raw21823step3 := by apply Matrix.ext; unfold raw21823step4 raw21823step3; decide +kernel
      have hl : raw21823step3Labels = labelEmbedding1 ∘ raw21823step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21823step3 raw21823step3Labels raw21823step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

def raw21824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21824step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21824step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21824step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw21824step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21824step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21824step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21824step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw21824step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21824 raw21824Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw21824 raw21824Labels = mixedMoment B raw21824step0 raw21824step0Labels := by
      have hz : ∀ j, raw21824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21824step0 = (fun i j => raw21824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21824step0 raw21824; decide +kernel
      have hl : raw21824step0Labels = raw21824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21824 raw21824Labels permutation346 hz
    mixedMoment B raw21824step0 raw21824step0Labels = mixedMoment B raw21824step1 raw21824step1Labels := by
      have hz : ∀ j, raw21824step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21824step1 = (fun i j => raw21824step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21824step1 raw21824step0; decide +kernel
      have hl : raw21824step1Labels = raw21824step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21824step0 raw21824step0Labels permutation56 hz
    mixedMoment B raw21824step1 raw21824step1Labels = mixedMoment B raw21824step2 raw21824step2Labels := by
      have ha : raw21824step2 = (fun i j => raw21824step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21824step2 raw21824step1; decide +kernel
      have hl : raw21824step2Labels = raw21824step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21824step1 raw21824step1Labels permutation8 permutation7
    mixedMoment B raw21824step2 raw21824step2Labels = mixedMoment B raw21824step3 raw21824step3Labels := by
      have ha : raw21824step3 = -raw21824step2 := by apply Matrix.ext; change ∀ i j, raw21824step3 i j = -(raw21824step2 i j); unfold raw21824step3 raw21824step2; decide +kernel
      have hl : raw21824step3Labels = raw21824step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21824step3 raw21824step3Labels = mixedMoment B raw21824step4 raw21824step4Labels := by
      have ha : raw21824step4 = raw21824step3 := by apply Matrix.ext; unfold raw21824step4 raw21824step3; decide +kernel
      have hl : raw21824step3Labels = labelEmbedding1 ∘ raw21824step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21824step3 raw21824step3Labels raw21824step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

def raw21825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21825step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw21825step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw21825step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21825step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw21825step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21825step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw21825step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21825step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw21825step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21825 raw21825Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw21825 raw21825Labels = mixedMoment B raw21825step0 raw21825step0Labels := by
      have hz : ∀ j, raw21825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21825step0 = (fun i j => raw21825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21825step0 raw21825; decide +kernel
      have hl : raw21825step0Labels = raw21825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21825 raw21825Labels permutation434 hz
    mixedMoment B raw21825step0 raw21825step0Labels = mixedMoment B raw21825step1 raw21825step1Labels := by
      have hz : ∀ j, raw21825step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21825step1 = (fun i j => raw21825step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21825step1 raw21825step0; decide +kernel
      have hl : raw21825step1Labels = raw21825step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21825step0 raw21825step0Labels permutation80 hz
    mixedMoment B raw21825step1 raw21825step1Labels = mixedMoment B raw21825step2 raw21825step2Labels := by
      have hz : ∀ j, raw21825step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21825step2 = (fun i j => raw21825step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21825step2 raw21825step1; decide +kernel
      have hl : raw21825step2Labels = raw21825step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21825step1 raw21825step1Labels permutation14 hz
    mixedMoment B raw21825step2 raw21825step2Labels = mixedMoment B raw21825step3 raw21825step3Labels := by
      have ha : raw21825step3 = (fun i j => raw21825step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21825step3 raw21825step2; decide +kernel
      have hl : raw21825step3Labels = raw21825step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21825step2 raw21825step2Labels permutation2 permutation7
    mixedMoment B raw21825step3 raw21825step3Labels = mixedMoment B raw21825step4 raw21825step4Labels := by
      have ha : raw21825step4 = -raw21825step3 := by apply Matrix.ext; change ∀ i j, raw21825step4 i j = -(raw21825step3 i j); unfold raw21825step4 raw21825step3; decide +kernel
      have hl : raw21825step4Labels = raw21825step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21825step4 raw21825step4Labels = mixedMoment B raw21825step5 raw21825step5Labels := by
      have ha : raw21825step5 = raw21825step4 := by apply Matrix.ext; unfold raw21825step5 raw21825step4; decide +kernel
      have hl : raw21825step4Labels = labelEmbedding1 ∘ raw21825step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21825step4 raw21825step4Labels raw21825step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1755 node1755Labels := by rfl

def raw21826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21826step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21826step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw21826step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21826step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, -2, 4]]
def raw21826step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21826step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw21826step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21826step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw21826step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21826 raw21826Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw21826 raw21826Labels = mixedMoment B raw21826step0 raw21826step0Labels := by
      have hz : ∀ j, raw21826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21826step0 = (fun i j => raw21826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21826step0 raw21826; decide +kernel
      have hl : raw21826step0Labels = raw21826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21826 raw21826Labels permutation434 hz
    mixedMoment B raw21826step0 raw21826step0Labels = mixedMoment B raw21826step1 raw21826step1Labels := by
      have hz : ∀ j, raw21826step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21826step1 = (fun i j => raw21826step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21826step1 raw21826step0; decide +kernel
      have hl : raw21826step1Labels = raw21826step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21826step0 raw21826step0Labels permutation80 hz
    mixedMoment B raw21826step1 raw21826step1Labels = mixedMoment B raw21826step2 raw21826step2Labels := by
      have hz : ∀ j, raw21826step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21826step2 = (fun i j => raw21826step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21826step2 raw21826step1; decide +kernel
      have hl : raw21826step2Labels = raw21826step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21826step1 raw21826step1Labels permutation14 hz
    mixedMoment B raw21826step2 raw21826step2Labels = mixedMoment B raw21826step3 raw21826step3Labels := by
      have ha : raw21826step3 = (fun i j => raw21826step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21826step3 raw21826step2; decide +kernel
      have hl : raw21826step3Labels = raw21826step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21826step2 raw21826step2Labels permutation2 permutation7
    mixedMoment B raw21826step3 raw21826step3Labels = mixedMoment B raw21826step4 raw21826step4Labels := by
      have ha : raw21826step4 = -raw21826step3 := by apply Matrix.ext; change ∀ i j, raw21826step4 i j = -(raw21826step3 i j); unfold raw21826step4 raw21826step3; decide +kernel
      have hl : raw21826step4Labels = raw21826step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21826step4 raw21826step4Labels = mixedMoment B raw21826step5 raw21826step5Labels := by
      have ha : raw21826step5 = raw21826step4 := by apply Matrix.ext; unfold raw21826step5 raw21826step4; decide +kernel
      have hl : raw21826step4Labels = labelEmbedding1 ∘ raw21826step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21826step4 raw21826step4Labels raw21826step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1537 node1537Labels := by rfl

def raw21827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21827step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21827step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw21827step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21827step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21827step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21827step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21827step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21827 raw21827Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw21827 raw21827Labels = mixedMoment B raw21827step0 raw21827step0Labels := by
      have hz : ∀ j, raw21827 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21827step0 = (fun i j => raw21827 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21827step0 raw21827; decide +kernel
      have hl : raw21827step0Labels = raw21827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21827 raw21827Labels permutation434 hz
    mixedMoment B raw21827step0 raw21827step0Labels = mixedMoment B raw21827step1 raw21827step1Labels := by
      have hz : ∀ j, raw21827step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21827step1 = (fun i j => raw21827step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21827step1 raw21827step0; decide +kernel
      have hl : raw21827step1Labels = raw21827step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21827step0 raw21827step0Labels permutation80 hz
    mixedMoment B raw21827step1 raw21827step1Labels = mixedMoment B raw21827step2 raw21827step2Labels := by
      have ha : raw21827step2 = (fun i j => raw21827step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21827step2 raw21827step1; decide +kernel
      have hl : raw21827step2Labels = raw21827step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21827step1 raw21827step1Labels permutation8 permutation7
    mixedMoment B raw21827step2 raw21827step2Labels = mixedMoment B raw21827step3 raw21827step3Labels := by
      have ha : raw21827step3 = -raw21827step2 := by apply Matrix.ext; change ∀ i j, raw21827step3 i j = -(raw21827step2 i j); unfold raw21827step3 raw21827step2; decide +kernel
      have hl : raw21827step3Labels = raw21827step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21827step3 raw21827step3Labels = mixedMoment B raw21827step4 raw21827step4Labels := by
      have ha : raw21827step4 = raw21827step3 := by apply Matrix.ext; unfold raw21827step4 raw21827step3; decide +kernel
      have hl : raw21827step3Labels = labelEmbedding1 ∘ raw21827step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21827step3 raw21827step3Labels raw21827step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw21828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21828step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21828step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21828step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw21828step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21828step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21828step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21828step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21828step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21828 raw21828Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw21828 raw21828Labels = mixedMoment B raw21828step0 raw21828step0Labels := by
      have hz : ∀ j, raw21828 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21828step0 = (fun i j => raw21828 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21828step0 raw21828; decide +kernel
      have hl : raw21828step0Labels = raw21828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21828 raw21828Labels permutation434 hz
    mixedMoment B raw21828step0 raw21828step0Labels = mixedMoment B raw21828step1 raw21828step1Labels := by
      have hz : ∀ j, raw21828step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21828step1 = (fun i j => raw21828step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21828step1 raw21828step0; decide +kernel
      have hl : raw21828step1Labels = raw21828step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21828step0 raw21828step0Labels permutation56 hz
    mixedMoment B raw21828step1 raw21828step1Labels = mixedMoment B raw21828step2 raw21828step2Labels := by
      have ha : raw21828step2 = (fun i j => raw21828step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21828step2 raw21828step1; decide +kernel
      have hl : raw21828step2Labels = raw21828step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21828step1 raw21828step1Labels permutation8 permutation7
    mixedMoment B raw21828step2 raw21828step2Labels = mixedMoment B raw21828step3 raw21828step3Labels := by
      have ha : raw21828step3 = -raw21828step2 := by apply Matrix.ext; change ∀ i j, raw21828step3 i j = -(raw21828step2 i j); unfold raw21828step3 raw21828step2; decide +kernel
      have hl : raw21828step3Labels = raw21828step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21828step3 raw21828step3Labels = mixedMoment B raw21828step4 raw21828step4Labels := by
      have ha : raw21828step4 = raw21828step3 := by apply Matrix.ext; unfold raw21828step4 raw21828step3; decide +kernel
      have hl : raw21828step3Labels = labelEmbedding1 ∘ raw21828step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21828step3 raw21828step3Labels raw21828step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw21829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21829Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21829step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21829step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw21829step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21829step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21829step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw21829step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21829 raw21829Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw21829 raw21829Labels = mixedMoment B raw21829step0 raw21829step0Labels := by
      have hz : ∀ j, raw21829 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21829step0 = (fun i j => raw21829 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21829step0 raw21829; decide +kernel
      have hl : raw21829step0Labels = raw21829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21829 raw21829Labels permutation346 hz
    mixedMoment B raw21829step0 raw21829step0Labels = mixedMoment B raw21829step1 raw21829step1Labels := by
      have hz : ∀ j, raw21829step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21829step1 = (fun i j => raw21829step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21829step1 raw21829step0; decide +kernel
      have hl : raw21829step1Labels = raw21829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21829step0 raw21829step0Labels permutation56 hz
    mixedMoment B raw21829step1 raw21829step1Labels = mixedMoment B raw21829step2 raw21829step2Labels := by
      have ha : raw21829step2 = (fun i j => raw21829step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21829step2 raw21829step1; decide +kernel
      have hl : raw21829step2Labels = raw21829step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21829step1 raw21829step1Labels permutation8 permutation7
    mixedMoment B raw21829step2 raw21829step2Labels = mixedMoment B raw21829step3 raw21829step3Labels := by
      have ha : raw21829step3 = -raw21829step2 := by apply Matrix.ext; change ∀ i j, raw21829step3 i j = -(raw21829step2 i j); unfold raw21829step3 raw21829step2; decide +kernel
      have hl : raw21829step3Labels = raw21829step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21829step3 raw21829step3Labels = mixedMoment B raw21829step4 raw21829step4Labels := by
      have ha : raw21829step4 = raw21829step3 := by apply Matrix.ext; unfold raw21829step4 raw21829step3; decide +kernel
      have hl : raw21829step3Labels = labelEmbedding1 ∘ raw21829step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21829step3 raw21829step3Labels raw21829step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw21830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21830Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21830step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw21830step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21830step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21830step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw21830step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21830step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw21830step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21830step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw21830step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21830 raw21830Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw21830 raw21830Labels = mixedMoment B raw21830step0 raw21830step0Labels := by
      have hz : ∀ j, raw21830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21830step0 = (fun i j => raw21830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21830step0 raw21830; decide +kernel
      have hl : raw21830step0Labels = raw21830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21830 raw21830Labels permutation434 hz
    mixedMoment B raw21830step0 raw21830step0Labels = mixedMoment B raw21830step1 raw21830step1Labels := by
      have hz : ∀ j, raw21830step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21830step1 = (fun i j => raw21830step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21830step1 raw21830step0; decide +kernel
      have hl : raw21830step1Labels = raw21830step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21830step0 raw21830step0Labels permutation80 hz
    mixedMoment B raw21830step1 raw21830step1Labels = mixedMoment B raw21830step2 raw21830step2Labels := by
      have hz : ∀ j, raw21830step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21830step2 = (fun i j => raw21830step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21830step2 raw21830step1; decide +kernel
      have hl : raw21830step2Labels = raw21830step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21830step1 raw21830step1Labels permutation14 hz
    mixedMoment B raw21830step2 raw21830step2Labels = mixedMoment B raw21830step3 raw21830step3Labels := by
      have ha : raw21830step3 = (fun i j => raw21830step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21830step3 raw21830step2; decide +kernel
      have hl : raw21830step3Labels = raw21830step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21830step2 raw21830step2Labels permutation2 permutation7
    mixedMoment B raw21830step3 raw21830step3Labels = mixedMoment B raw21830step4 raw21830step4Labels := by
      have ha : raw21830step4 = -raw21830step3 := by apply Matrix.ext; change ∀ i j, raw21830step4 i j = -(raw21830step3 i j); unfold raw21830step4 raw21830step3; decide +kernel
      have hl : raw21830step4Labels = raw21830step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21830step4 raw21830step4Labels = mixedMoment B raw21830step5 raw21830step5Labels := by
      have ha : raw21830step5 = raw21830step4 := by apply Matrix.ext; unfold raw21830step5 raw21830step4; decide +kernel
      have hl : raw21830step4Labels = labelEmbedding1 ∘ raw21830step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21830step4 raw21830step4Labels raw21830step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw21831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21831 raw21831Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw21831 raw21831Labels = mixedMoment B raw21831step0 raw21831step0Labels := by
      have hz : ∀ j, raw21831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21831step0 = (fun i j => raw21831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21831step0 raw21831; decide +kernel
      have hl : raw21831step0Labels = raw21831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21831 raw21831Labels permutation434 hz
    mixedMoment B raw21831step0 raw21831step0Labels = mixedMoment B raw21831step1 raw21831step1Labels := by
      have hz : ∀ j, raw21831step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21831step1 = (fun i j => raw21831step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21831step1 raw21831step0; decide +kernel
      have hl : raw21831step1Labels = raw21831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21831step0 raw21831step0Labels permutation80 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

def raw21832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21832 raw21832Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw21832 raw21832Labels = mixedMoment B raw21832step0 raw21832step0Labels := by
      have hz : ∀ j, raw21832 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21832step0 = (fun i j => raw21832 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21832step0 raw21832; decide +kernel
      have hl : raw21832step0Labels = raw21832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21832 raw21832Labels permutation434 hz
    mixedMoment B raw21832step0 raw21832step0Labels = mixedMoment B raw21832step1 raw21832step1Labels := by
      have hz : ∀ j, raw21832step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21832step1 = (fun i j => raw21832step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21832step1 raw21832step0; decide +kernel
      have hl : raw21832step1Labels = raw21832step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21832step0 raw21832step0Labels permutation56 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

def raw21833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21833 raw21833Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw21833 raw21833Labels = mixedMoment B raw21833step0 raw21833step0Labels := by
      have hz : ∀ j, raw21833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21833step0 = (fun i j => raw21833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21833step0 raw21833; decide +kernel
      have hl : raw21833step0Labels = raw21833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21833 raw21833Labels permutation346 hz
    mixedMoment B raw21833step0 raw21833step0Labels = mixedMoment B raw21833step1 raw21833step1Labels := by
      have hz : ∀ j, raw21833step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21833step1 = (fun i j => raw21833step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21833step1 raw21833step0; decide +kernel
      have hl : raw21833step1Labels = raw21833step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21833step0 raw21833step0Labels permutation56 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

def raw21834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21834step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw21834step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21834step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21834step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21834step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21834step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21834 raw21834Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw21834 raw21834Labels = mixedMoment B raw21834step0 raw21834step0Labels := by
      have hz : ∀ j, raw21834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21834step0 = (fun i j => raw21834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21834step0 raw21834; decide +kernel
      have hl : raw21834step0Labels = raw21834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21834 raw21834Labels permutation434 hz
    mixedMoment B raw21834step0 raw21834step0Labels = mixedMoment B raw21834step1 raw21834step1Labels := by
      have hz : ∀ j, raw21834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21834step1 = (fun i j => raw21834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21834step1 raw21834step0; decide +kernel
      have hl : raw21834step1Labels = raw21834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21834step0 raw21834step0Labels permutation80 hz
    mixedMoment B raw21834step1 raw21834step1Labels = mixedMoment B raw21834step2 raw21834step2Labels := by
      have hz : ∀ j, raw21834step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21834step2 = (fun i j => raw21834step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21834step2 raw21834step1; decide +kernel
      have hl : raw21834step2Labels = raw21834step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21834step1 raw21834step1Labels permutation14 hz
    mixedMoment B raw21834step2 raw21834step2Labels = mixedMoment B raw21834step3 raw21834step3Labels := by
      have ha : raw21834step3 = (fun i j => raw21834step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21834step3 raw21834step2; decide +kernel
      have hl : raw21834step3Labels = raw21834step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21834step2 raw21834step2Labels permutation2 permutation7
    mixedMoment B raw21834step3 raw21834step3Labels = mixedMoment B raw21834step4 raw21834step4Labels := by
      have ha : raw21834step4 = -raw21834step3 := by apply Matrix.ext; change ∀ i j, raw21834step4 i j = -(raw21834step3 i j); unfold raw21834step4 raw21834step3; decide +kernel
      have hl : raw21834step4Labels = raw21834step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21834step4 raw21834step4Labels = mixedMoment B raw21834step5 raw21834step5Labels := by
      have ha : raw21834step5 = raw21834step4 := by apply Matrix.ext; unfold raw21834step5 raw21834step4; decide +kernel
      have hl : raw21834step4Labels = labelEmbedding10 ∘ raw21834step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21834step4 raw21834step4Labels raw21834step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw21835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21835 raw21835Labels = mixedMoment B node4174 node4174Labels := by
  calc
    mixedMoment B raw21835 raw21835Labels = mixedMoment B raw21835step0 raw21835step0Labels := by
      have hz : ∀ j, raw21835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21835step0 = (fun i j => raw21835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21835step0 raw21835; decide +kernel
      have hl : raw21835step0Labels = raw21835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21835 raw21835Labels permutation434 hz
    mixedMoment B raw21835step0 raw21835step0Labels = mixedMoment B raw21835step1 raw21835step1Labels := by
      have hz : ∀ j, raw21835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21835step1 = (fun i j => raw21835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21835step1 raw21835step0; decide +kernel
      have hl : raw21835step1Labels = raw21835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21835step0 raw21835step0Labels permutation80 hz
    _ = mixedMoment B node4174 node4174Labels := by rfl

def raw21836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21836 raw21836Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21836 raw21836Labels = mixedMoment B raw21836step0 raw21836step0Labels := by
      have hz : ∀ j, raw21836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21836step0 = (fun i j => raw21836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21836step0 raw21836; decide +kernel
      have hl : raw21836step0Labels = raw21836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21836 raw21836Labels permutation434 hz
    mixedMoment B raw21836step0 raw21836step0Labels = mixedMoment B raw21836step1 raw21836step1Labels := by
      have ha : raw21836step1 = (fun i j => raw21836step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21836step1 raw21836step0; decide +kernel
      have hl : raw21836step1Labels = raw21836step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21836step0 raw21836step0Labels permutation38 permutation2
    _ = mixedMoment B node4343 node4343Labels := by rfl

def raw21837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21837 raw21837Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21837 raw21837Labels = mixedMoment B raw21837step0 raw21837step0Labels := by
      have hz : ∀ j, raw21837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21837step0 = (fun i j => raw21837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21837step0 raw21837; decide +kernel
      have hl : raw21837step0Labels = raw21837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21837 raw21837Labels permutation346 hz
    mixedMoment B raw21837step0 raw21837step0Labels = mixedMoment B raw21837step1 raw21837step1Labels := by
      have ha : raw21837step1 = (fun i j => raw21837step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21837step1 raw21837step0; decide +kernel
      have hl : raw21837step1Labels = raw21837step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21837step0 raw21837step0Labels permutation38 permutation2
    _ = mixedMoment B node4343 node4343Labels := by rfl

def raw21838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21838 raw21838Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw21838 raw21838Labels = mixedMoment B raw21838step0 raw21838step0Labels := by
      have hz : ∀ j, raw21838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21838step0 = (fun i j => raw21838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21838step0 raw21838; decide +kernel
      have hl : raw21838step0Labels = raw21838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21838 raw21838Labels permutation434 hz
    mixedMoment B raw21838step0 raw21838step0Labels = mixedMoment B raw21838step1 raw21838step1Labels := by
      have hz : ∀ j, raw21838step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21838step1 = (fun i j => raw21838step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21838step1 raw21838step0; decide +kernel
      have hl : raw21838step1Labels = raw21838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21838step0 raw21838step0Labels permutation80 hz
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw21839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21839 raw21839Labels = mixedMoment B node4174 node4174Labels := by
  calc
    mixedMoment B raw21839 raw21839Labels = mixedMoment B raw21839step0 raw21839step0Labels := by
      have hz : ∀ j, raw21839 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21839step0 = (fun i j => raw21839 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21839step0 raw21839; decide +kernel
      have hl : raw21839step0Labels = raw21839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21839 raw21839Labels permutation434 hz
    mixedMoment B raw21839step0 raw21839step0Labels = mixedMoment B raw21839step1 raw21839step1Labels := by
      have hz : ∀ j, raw21839step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21839step1 = (fun i j => raw21839step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21839step1 raw21839step0; decide +kernel
      have hl : raw21839step1Labels = raw21839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21839step0 raw21839step0Labels permutation56 hz
    _ = mixedMoment B node4174 node4174Labels := by rfl

def raw21840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21840 raw21840Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21840 raw21840Labels = mixedMoment B raw21840step0 raw21840step0Labels := by
      have hz : ∀ j, raw21840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21840step0 = (fun i j => raw21840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21840step0 raw21840; decide +kernel
      have hl : raw21840step0Labels = raw21840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21840 raw21840Labels permutation434 hz
    _ = mixedMoment B node4343 node4343Labels := by rfl

def raw21841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21841 raw21841Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21841 raw21841Labels = mixedMoment B raw21841step0 raw21841step0Labels := by
      have hz : ∀ j, raw21841 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21841step0 = (fun i j => raw21841 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21841step0 raw21841; decide +kernel
      have hl : raw21841step0Labels = raw21841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21841 raw21841Labels permutation265 hz
    mixedMoment B raw21841step0 raw21841step0Labels = mixedMoment B raw21841step1 raw21841step1Labels := by
      have ha : raw21841step1 = (fun i j => raw21841step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21841step1 raw21841step0; decide +kernel
      have hl : raw21841step1Labels = raw21841step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21841step0 raw21841step0Labels permutation38 permutation2
    _ = mixedMoment B node4343 node4343Labels := by rfl

def raw21842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21842step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21842 raw21842Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw21842 raw21842Labels = mixedMoment B raw21842step0 raw21842step0Labels := by
      have hz : ∀ j, raw21842 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21842step0 = (fun i j => raw21842 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21842step0 raw21842; decide +kernel
      have hl : raw21842step0Labels = raw21842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21842 raw21842Labels permutation434 hz
    mixedMoment B raw21842step0 raw21842step0Labels = mixedMoment B raw21842step1 raw21842step1Labels := by
      have hz : ∀ j, raw21842step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21842step1 = (fun i j => raw21842step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21842step1 raw21842step0; decide +kernel
      have hl : raw21842step1Labels = raw21842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21842step0 raw21842step0Labels permutation56 hz
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw21843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21843step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21843 raw21843Labels = mixedMoment B node4174 node4174Labels := by
  calc
    mixedMoment B raw21843 raw21843Labels = mixedMoment B raw21843step0 raw21843step0Labels := by
      have hz : ∀ j, raw21843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21843step0 = (fun i j => raw21843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21843step0 raw21843; decide +kernel
      have hl : raw21843step0Labels = raw21843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21843 raw21843Labels permutation346 hz
    mixedMoment B raw21843step0 raw21843step0Labels = mixedMoment B raw21843step1 raw21843step1Labels := by
      have hz : ∀ j, raw21843step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21843step1 = (fun i j => raw21843step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21843step1 raw21843step0; decide +kernel
      have hl : raw21843step1Labels = raw21843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21843step0 raw21843step0Labels permutation56 hz
    _ = mixedMoment B node4174 node4174Labels := by rfl

def raw21844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21844 raw21844Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21844 raw21844Labels = mixedMoment B raw21844step0 raw21844step0Labels := by
      have hz : ∀ j, raw21844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21844step0 = (fun i j => raw21844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21844step0 raw21844; decide +kernel
      have hl : raw21844step0Labels = raw21844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21844 raw21844Labels permutation346 hz
    _ = mixedMoment B node4343 node4343Labels := by rfl

def raw21845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21845 raw21845Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21845 raw21845Labels = mixedMoment B raw21845step0 raw21845step0Labels := by
      have hz : ∀ j, raw21845 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21845step0 = (fun i j => raw21845 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21845step0 raw21845; decide +kernel
      have hl : raw21845step0Labels = raw21845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21845 raw21845Labels permutation265 hz
    _ = mixedMoment B node4343 node4343Labels := by rfl

def raw21846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21846 raw21846Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw21846 raw21846Labels = mixedMoment B raw21846step0 raw21846step0Labels := by
      have hz : ∀ j, raw21846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21846step0 = (fun i j => raw21846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21846step0 raw21846; decide +kernel
      have hl : raw21846step0Labels = raw21846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21846 raw21846Labels permutation346 hz
    mixedMoment B raw21846step0 raw21846step0Labels = mixedMoment B raw21846step1 raw21846step1Labels := by
      have hz : ∀ j, raw21846step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21846step1 = (fun i j => raw21846step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21846step1 raw21846step0; decide +kernel
      have hl : raw21846step1Labels = raw21846step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21846step0 raw21846step0Labels permutation56 hz
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw21847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21847step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw21847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21847 raw21847Labels = mixedMoment B node4190 node4190Labels := by
  calc
    mixedMoment B raw21847 raw21847Labels = mixedMoment B raw21847step0 raw21847step0Labels := by
      have hz : ∀ j, raw21847 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21847step0 = (fun i j => raw21847 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21847step0 raw21847; decide +kernel
      have hl : raw21847step0Labels = raw21847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21847 raw21847Labels permutation434 hz
    mixedMoment B raw21847step0 raw21847step0Labels = mixedMoment B raw21847step1 raw21847step1Labels := by
      have hz : ∀ j, raw21847step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21847step1 = (fun i j => raw21847step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21847step1 raw21847step0; decide +kernel
      have hl : raw21847step1Labels = raw21847step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21847step0 raw21847step0Labels permutation80 hz
    mixedMoment B raw21847step1 raw21847step1Labels = mixedMoment B raw21847step2 raw21847step2Labels := by
      have hz : ∀ j, raw21847step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21847step2 = (fun i j => raw21847step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21847step2 raw21847step1; decide +kernel
      have hl : raw21847step2Labels = raw21847step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21847step1 raw21847step1Labels permutation14 hz
    _ = mixedMoment B node4190 node4190Labels := by rfl

def raw21848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21848 raw21848Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw21848 raw21848Labels = mixedMoment B raw21848step0 raw21848step0Labels := by
      have hz : ∀ j, raw21848 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21848step0 = (fun i j => raw21848 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21848step0 raw21848; decide +kernel
      have hl : raw21848step0Labels = raw21848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21848 raw21848Labels permutation434 hz
    mixedMoment B raw21848step0 raw21848step0Labels = mixedMoment B raw21848step1 raw21848step1Labels := by
      have hz : ∀ j, raw21848step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21848step1 = (fun i j => raw21848step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21848step1 raw21848step0; decide +kernel
      have hl : raw21848step1Labels = raw21848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21848step0 raw21848step0Labels permutation80 hz
    _ = mixedMoment B node4359 node4359Labels := by rfl

def raw21849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21849 raw21849Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw21849 raw21849Labels = mixedMoment B raw21849step0 raw21849step0Labels := by
      have hz : ∀ j, raw21849 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21849step0 = (fun i j => raw21849 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21849step0 raw21849; decide +kernel
      have hl : raw21849step0Labels = raw21849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21849 raw21849Labels permutation434 hz
    mixedMoment B raw21849step0 raw21849step0Labels = mixedMoment B raw21849step1 raw21849step1Labels := by
      have hz : ∀ j, raw21849step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21849step1 = (fun i j => raw21849step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21849step1 raw21849step0; decide +kernel
      have hl : raw21849step1Labels = raw21849step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21849step0 raw21849step0Labels permutation56 hz
    _ = mixedMoment B node4359 node4359Labels := by rfl

def raw21850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21850 raw21850Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw21850 raw21850Labels = mixedMoment B raw21850step0 raw21850step0Labels := by
      have hz : ∀ j, raw21850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21850step0 = (fun i j => raw21850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21850step0 raw21850; decide +kernel
      have hl : raw21850step0Labels = raw21850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21850 raw21850Labels permutation346 hz
    mixedMoment B raw21850step0 raw21850step0Labels = mixedMoment B raw21850step1 raw21850step1Labels := by
      have hz : ∀ j, raw21850step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21850step1 = (fun i j => raw21850step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21850step1 raw21850step0; decide +kernel
      have hl : raw21850step1Labels = raw21850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21850step0 raw21850step0Labels permutation56 hz
    _ = mixedMoment B node4359 node4359Labels := by rfl

def raw21851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21851step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw21851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21851 raw21851Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw21851 raw21851Labels = mixedMoment B raw21851step0 raw21851step0Labels := by
      have hz : ∀ j, raw21851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21851step0 = (fun i j => raw21851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21851step0 raw21851; decide +kernel
      have hl : raw21851step0Labels = raw21851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21851 raw21851Labels permutation434 hz
    mixedMoment B raw21851step0 raw21851step0Labels = mixedMoment B raw21851step1 raw21851step1Labels := by
      have hz : ∀ j, raw21851step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21851step1 = (fun i j => raw21851step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21851step1 raw21851step0; decide +kernel
      have hl : raw21851step1Labels = raw21851step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21851step0 raw21851step0Labels permutation80 hz
    mixedMoment B raw21851step1 raw21851step1Labels = mixedMoment B raw21851step2 raw21851step2Labels := by
      have hz : ∀ j, raw21851step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21851step2 = (fun i j => raw21851step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21851step2 raw21851step1; decide +kernel
      have hl : raw21851step2Labels = raw21851step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21851step1 raw21851step1Labels permutation14 hz
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw21852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![4, -1, -3]]
def raw21852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21852step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw21852step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21852 raw21852Labels = mixedMoment B node4512 node4512Labels := by
  calc
    mixedMoment B raw21852 raw21852Labels = mixedMoment B raw21852step0 raw21852step0Labels := by
      have hz : ∀ j, raw21852 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21852step0 = (fun i j => raw21852 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21852step0 raw21852; decide +kernel
      have hl : raw21852step0Labels = raw21852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21852 raw21852Labels permutation520 hz
    mixedMoment B raw21852step0 raw21852step0Labels = mixedMoment B raw21852step1 raw21852step1Labels := by
      have hz : ∀ j, raw21852step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21852step1 = (fun i j => raw21852step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21852step1 raw21852step0; decide +kernel
      have hl : raw21852step1Labels = raw21852step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21852step0 raw21852step0Labels permutation104 hz
    mixedMoment B raw21852step1 raw21852step1Labels = mixedMoment B raw21852step2 raw21852step2Labels := by
      have hz : ∀ j, raw21852step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21852step2 = (fun i j => raw21852step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21852step2 raw21852step1; decide +kernel
      have hl : raw21852step2Labels = raw21852step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21852step1 raw21852step1Labels permutation20 hz
    mixedMoment B raw21852step2 raw21852step2Labels = mixedMoment B raw21852step3 raw21852step3Labels := by
      have hz : ∀ j, raw21852step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw21852step3 = (fun i j => raw21852step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw21852step3 raw21852step2; decide +kernel
      have hl : raw21852step3Labels = raw21852step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21852step2 raw21852step2Labels permutation4 hz
    _ = mixedMoment B node4512 node4512Labels := by rfl

def raw21853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21853step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21853step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21853step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21853step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21853step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21853 raw21853Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw21853 raw21853Labels = mixedMoment B raw21853step0 raw21853step0Labels := by
      have hz : ∀ j, raw21853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21853step0 = (fun i j => raw21853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21853step0 raw21853; decide +kernel
      have hl : raw21853step0Labels = raw21853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21853 raw21853Labels permutation434 hz
    mixedMoment B raw21853step0 raw21853step0Labels = mixedMoment B raw21853step1 raw21853step1Labels := by
      have hz : ∀ j, raw21853step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21853step1 = (fun i j => raw21853step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21853step1 raw21853step0; decide +kernel
      have hl : raw21853step1Labels = raw21853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21853step0 raw21853step0Labels permutation80 hz
    mixedMoment B raw21853step1 raw21853step1Labels = mixedMoment B raw21853step2 raw21853step2Labels := by
      have ha : raw21853step2 = (fun i j => raw21853step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21853step2 raw21853step1; decide +kernel
      have hl : raw21853step2Labels = raw21853step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21853step1 raw21853step1Labels permutation31 permutation7
    mixedMoment B raw21853step2 raw21853step2Labels = mixedMoment B raw21853step3 raw21853step3Labels := by
      have ha : raw21853step3 = raw21853step2 := by apply Matrix.ext; unfold raw21853step3 raw21853step2; decide +kernel
      have hl : raw21853step2Labels = labelEmbedding1 ∘ raw21853step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21853step2 raw21853step2Labels raw21853step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

def raw21854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21854step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21854step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21854step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21854step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21854step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21854 raw21854Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw21854 raw21854Labels = mixedMoment B raw21854step0 raw21854step0Labels := by
      have hz : ∀ j, raw21854 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21854step0 = (fun i j => raw21854 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21854step0 raw21854; decide +kernel
      have hl : raw21854step0Labels = raw21854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21854 raw21854Labels permutation434 hz
    mixedMoment B raw21854step0 raw21854step0Labels = mixedMoment B raw21854step1 raw21854step1Labels := by
      have hz : ∀ j, raw21854step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21854step1 = (fun i j => raw21854step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21854step1 raw21854step0; decide +kernel
      have hl : raw21854step1Labels = raw21854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21854step0 raw21854step0Labels permutation56 hz
    mixedMoment B raw21854step1 raw21854step1Labels = mixedMoment B raw21854step2 raw21854step2Labels := by
      have ha : raw21854step2 = (fun i j => raw21854step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21854step2 raw21854step1; decide +kernel
      have hl : raw21854step2Labels = raw21854step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21854step1 raw21854step1Labels permutation31 permutation7
    mixedMoment B raw21854step2 raw21854step2Labels = mixedMoment B raw21854step3 raw21854step3Labels := by
      have ha : raw21854step3 = raw21854step2 := by apply Matrix.ext; unfold raw21854step3 raw21854step2; decide +kernel
      have hl : raw21854step2Labels = labelEmbedding1 ∘ raw21854step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21854step2 raw21854step2Labels raw21854step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

def raw21855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21855step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21855step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21855step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21855 raw21855Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw21855 raw21855Labels = mixedMoment B raw21855step0 raw21855step0Labels := by
      have hz : ∀ j, raw21855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21855step0 = (fun i j => raw21855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21855step0 raw21855; decide +kernel
      have hl : raw21855step0Labels = raw21855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21855 raw21855Labels permutation346 hz
    mixedMoment B raw21855step0 raw21855step0Labels = mixedMoment B raw21855step1 raw21855step1Labels := by
      have hz : ∀ j, raw21855step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21855step1 = (fun i j => raw21855step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21855step1 raw21855step0; decide +kernel
      have hl : raw21855step1Labels = raw21855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21855step0 raw21855step0Labels permutation56 hz
    mixedMoment B raw21855step1 raw21855step1Labels = mixedMoment B raw21855step2 raw21855step2Labels := by
      have ha : raw21855step2 = (fun i j => raw21855step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21855step2 raw21855step1; decide +kernel
      have hl : raw21855step2Labels = raw21855step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21855step1 raw21855step1Labels permutation31 permutation7
    mixedMoment B raw21855step2 raw21855step2Labels = mixedMoment B raw21855step3 raw21855step3Labels := by
      have ha : raw21855step3 = raw21855step2 := by apply Matrix.ext; unfold raw21855step3 raw21855step2; decide +kernel
      have hl : raw21855step2Labels = labelEmbedding1 ∘ raw21855step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21855step2 raw21855step2Labels raw21855step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

def raw21856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21856step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21856step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21856step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21856step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw21856step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21856step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21856step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21856step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21856step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21856 raw21856Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw21856 raw21856Labels = mixedMoment B raw21856step0 raw21856step0Labels := by
      have hz : ∀ j, raw21856 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21856step0 = (fun i j => raw21856 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21856step0 raw21856; decide +kernel
      have hl : raw21856step0Labels = raw21856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21856 raw21856Labels permutation434 hz
    mixedMoment B raw21856step0 raw21856step0Labels = mixedMoment B raw21856step1 raw21856step1Labels := by
      have hz : ∀ j, raw21856step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21856step1 = (fun i j => raw21856step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21856step1 raw21856step0; decide +kernel
      have hl : raw21856step1Labels = raw21856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21856step0 raw21856step0Labels permutation80 hz
    mixedMoment B raw21856step1 raw21856step1Labels = mixedMoment B raw21856step2 raw21856step2Labels := by
      have hz : ∀ j, raw21856step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21856step2 = (fun i j => raw21856step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21856step2 raw21856step1; decide +kernel
      have hl : raw21856step2Labels = raw21856step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21856step1 raw21856step1Labels permutation14 hz
    mixedMoment B raw21856step2 raw21856step2Labels = mixedMoment B raw21856step3 raw21856step3Labels := by
      have ha : raw21856step3 = (fun i j => raw21856step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21856step3 raw21856step2; decide +kernel
      have hl : raw21856step3Labels = raw21856step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21856step2 raw21856step2Labels permutation2 permutation7
    mixedMoment B raw21856step3 raw21856step3Labels = mixedMoment B raw21856step4 raw21856step4Labels := by
      have ha : raw21856step4 = -raw21856step3 := by apply Matrix.ext; change ∀ i j, raw21856step4 i j = -(raw21856step3 i j); unfold raw21856step4 raw21856step3; decide +kernel
      have hl : raw21856step4Labels = raw21856step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21856step4 raw21856step4Labels = mixedMoment B raw21856step5 raw21856step5Labels := by
      have ha : raw21856step5 = raw21856step4 := by apply Matrix.ext; unfold raw21856step5 raw21856step4; decide +kernel
      have hl : raw21856step4Labels = labelEmbedding1 ∘ raw21856step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21856step4 raw21856step4Labels raw21856step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw21857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21857step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21857step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21857step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21857step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21857step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21857step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21857step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21857 raw21857Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw21857 raw21857Labels = mixedMoment B raw21857step0 raw21857step0Labels := by
      have hz : ∀ j, raw21857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21857step0 = (fun i j => raw21857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21857step0 raw21857; decide +kernel
      have hl : raw21857step0Labels = raw21857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21857 raw21857Labels permutation434 hz
    mixedMoment B raw21857step0 raw21857step0Labels = mixedMoment B raw21857step1 raw21857step1Labels := by
      have hz : ∀ j, raw21857step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21857step1 = (fun i j => raw21857step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21857step1 raw21857step0; decide +kernel
      have hl : raw21857step1Labels = raw21857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21857step0 raw21857step0Labels permutation80 hz
    mixedMoment B raw21857step1 raw21857step1Labels = mixedMoment B raw21857step2 raw21857step2Labels := by
      have ha : raw21857step2 = (fun i j => raw21857step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21857step2 raw21857step1; decide +kernel
      have hl : raw21857step2Labels = raw21857step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21857step1 raw21857step1Labels permutation8 permutation7
    mixedMoment B raw21857step2 raw21857step2Labels = mixedMoment B raw21857step3 raw21857step3Labels := by
      have ha : raw21857step3 = -raw21857step2 := by apply Matrix.ext; change ∀ i j, raw21857step3 i j = -(raw21857step2 i j); unfold raw21857step3 raw21857step2; decide +kernel
      have hl : raw21857step3Labels = raw21857step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21857step3 raw21857step3Labels = mixedMoment B raw21857step4 raw21857step4Labels := by
      have ha : raw21857step4 = raw21857step3 := by apply Matrix.ext; unfold raw21857step4 raw21857step3; decide +kernel
      have hl : raw21857step3Labels = labelEmbedding1 ∘ raw21857step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21857step3 raw21857step3Labels raw21857step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1509 node1509Labels := by rfl

def raw21858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21858step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21858step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21858step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21858step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21858 raw21858Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21858 raw21858Labels = mixedMoment B raw21858step0 raw21858step0Labels := by
      have hz : ∀ j, raw21858 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21858step0 = (fun i j => raw21858 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21858step0 raw21858; decide +kernel
      have hl : raw21858step0Labels = raw21858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21858 raw21858Labels permutation434 hz
    mixedMoment B raw21858step0 raw21858step0Labels = mixedMoment B raw21858step1 raw21858step1Labels := by
      have ha : raw21858step1 = (fun i j => raw21858step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21858step1 raw21858step0; decide +kernel
      have hl : raw21858step1Labels = raw21858step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21858step0 raw21858step0Labels permutation38 permutation7
    mixedMoment B raw21858step1 raw21858step1Labels = mixedMoment B raw21858step2 raw21858step2Labels := by
      have ha : raw21858step2 = -raw21858step1 := by apply Matrix.ext; change ∀ i j, raw21858step2 i j = -(raw21858step1 i j); unfold raw21858step2 raw21858step1; decide +kernel
      have hl : raw21858step2Labels = raw21858step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21858step2 raw21858step2Labels = mixedMoment B raw21858step3 raw21858step3Labels := by
      have ha : raw21858step3 = raw21858step2 := by apply Matrix.ext; unfold raw21858step3 raw21858step2; decide +kernel
      have hl : raw21858step2Labels = labelEmbedding1 ∘ raw21858step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21858step2 raw21858step2Labels raw21858step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

def raw21859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21859step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21859step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21859step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21859 raw21859Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21859 raw21859Labels = mixedMoment B raw21859step0 raw21859step0Labels := by
      have hz : ∀ j, raw21859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21859step0 = (fun i j => raw21859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21859step0 raw21859; decide +kernel
      have hl : raw21859step0Labels = raw21859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21859 raw21859Labels permutation346 hz
    mixedMoment B raw21859step0 raw21859step0Labels = mixedMoment B raw21859step1 raw21859step1Labels := by
      have ha : raw21859step1 = (fun i j => raw21859step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21859step1 raw21859step0; decide +kernel
      have hl : raw21859step1Labels = raw21859step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21859step0 raw21859step0Labels permutation38 permutation7
    mixedMoment B raw21859step1 raw21859step1Labels = mixedMoment B raw21859step2 raw21859step2Labels := by
      have ha : raw21859step2 = -raw21859step1 := by apply Matrix.ext; change ∀ i j, raw21859step2 i j = -(raw21859step1 i j); unfold raw21859step2 raw21859step1; decide +kernel
      have hl : raw21859step2Labels = raw21859step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21859step2 raw21859step2Labels = mixedMoment B raw21859step3 raw21859step3Labels := by
      have ha : raw21859step3 = raw21859step2 := by apply Matrix.ext; unfold raw21859step3 raw21859step2; decide +kernel
      have hl : raw21859step2Labels = labelEmbedding1 ∘ raw21859step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21859step2 raw21859step2Labels raw21859step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

def raw21860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21860step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21860step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21860step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21860step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21860step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21860step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21860step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21860 raw21860Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw21860 raw21860Labels = mixedMoment B raw21860step0 raw21860step0Labels := by
      have hz : ∀ j, raw21860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21860step0 = (fun i j => raw21860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21860step0 raw21860; decide +kernel
      have hl : raw21860step0Labels = raw21860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21860 raw21860Labels permutation434 hz
    mixedMoment B raw21860step0 raw21860step0Labels = mixedMoment B raw21860step1 raw21860step1Labels := by
      have hz : ∀ j, raw21860step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21860step1 = (fun i j => raw21860step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21860step1 raw21860step0; decide +kernel
      have hl : raw21860step1Labels = raw21860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21860step0 raw21860step0Labels permutation80 hz
    mixedMoment B raw21860step1 raw21860step1Labels = mixedMoment B raw21860step2 raw21860step2Labels := by
      have ha : raw21860step2 = (fun i j => raw21860step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21860step2 raw21860step1; decide +kernel
      have hl : raw21860step2Labels = raw21860step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21860step1 raw21860step1Labels permutation8 permutation7
    mixedMoment B raw21860step2 raw21860step2Labels = mixedMoment B raw21860step3 raw21860step3Labels := by
      have ha : raw21860step3 = -raw21860step2 := by apply Matrix.ext; change ∀ i j, raw21860step3 i j = -(raw21860step2 i j); unfold raw21860step3 raw21860step2; decide +kernel
      have hl : raw21860step3Labels = raw21860step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21860step3 raw21860step3Labels = mixedMoment B raw21860step4 raw21860step4Labels := by
      have ha : raw21860step4 = raw21860step3 := by apply Matrix.ext; unfold raw21860step4 raw21860step3; decide +kernel
      have hl : raw21860step3Labels = labelEmbedding1 ∘ raw21860step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21860step3 raw21860step3Labels raw21860step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw21861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21861step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21861step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21861step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21861step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21861 raw21861Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw21861 raw21861Labels = mixedMoment B raw21861step0 raw21861step0Labels := by
      have hz : ∀ j, raw21861 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21861step0 = (fun i j => raw21861 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21861step0 raw21861; decide +kernel
      have hl : raw21861step0Labels = raw21861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21861 raw21861Labels permutation434 hz
    mixedMoment B raw21861step0 raw21861step0Labels = mixedMoment B raw21861step1 raw21861step1Labels := by
      have hz : ∀ j, raw21861step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21861step1 = (fun i j => raw21861step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21861step1 raw21861step0; decide +kernel
      have hl : raw21861step1Labels = raw21861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21861step0 raw21861step0Labels permutation56 hz
    mixedMoment B raw21861step1 raw21861step1Labels = mixedMoment B raw21861step2 raw21861step2Labels := by
      have ha : raw21861step2 = (fun i j => raw21861step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21861step2 raw21861step1; decide +kernel
      have hl : raw21861step2Labels = raw21861step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21861step1 raw21861step1Labels permutation8 permutation7
    mixedMoment B raw21861step2 raw21861step2Labels = mixedMoment B raw21861step3 raw21861step3Labels := by
      have ha : raw21861step3 = -raw21861step2 := by apply Matrix.ext; change ∀ i j, raw21861step3 i j = -(raw21861step2 i j); unfold raw21861step3 raw21861step2; decide +kernel
      have hl : raw21861step3Labels = raw21861step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21861step3 raw21861step3Labels = mixedMoment B raw21861step4 raw21861step4Labels := by
      have ha : raw21861step4 = raw21861step3 := by apply Matrix.ext; unfold raw21861step4 raw21861step3; decide +kernel
      have hl : raw21861step3Labels = labelEmbedding1 ∘ raw21861step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21861step3 raw21861step3Labels raw21861step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1509 node1509Labels := by rfl

def raw21862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21862step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21862step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21862step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21862step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21862 raw21862Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21862 raw21862Labels = mixedMoment B raw21862step0 raw21862step0Labels := by
      have hz : ∀ j, raw21862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21862step0 = (fun i j => raw21862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21862step0 raw21862; decide +kernel
      have hl : raw21862step0Labels = raw21862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21862 raw21862Labels permutation434 hz
    mixedMoment B raw21862step0 raw21862step0Labels = mixedMoment B raw21862step1 raw21862step1Labels := by
      have ha : raw21862step1 = (fun i j => raw21862step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21862step1 raw21862step0; decide +kernel
      have hl : raw21862step1Labels = raw21862step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21862step0 raw21862step0Labels permutation32 permutation7
    mixedMoment B raw21862step1 raw21862step1Labels = mixedMoment B raw21862step2 raw21862step2Labels := by
      have ha : raw21862step2 = -raw21862step1 := by apply Matrix.ext; change ∀ i j, raw21862step2 i j = -(raw21862step1 i j); unfold raw21862step2 raw21862step1; decide +kernel
      have hl : raw21862step2Labels = raw21862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21862step2 raw21862step2Labels = mixedMoment B raw21862step3 raw21862step3Labels := by
      have ha : raw21862step3 = raw21862step2 := by apply Matrix.ext; unfold raw21862step3 raw21862step2; decide +kernel
      have hl : raw21862step2Labels = labelEmbedding1 ∘ raw21862step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21862step2 raw21862step2Labels raw21862step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

def raw21863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21863step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21863step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21863step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21863step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21863step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21863 raw21863Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21863 raw21863Labels = mixedMoment B raw21863step0 raw21863step0Labels := by
      have hz : ∀ j, raw21863 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21863step0 = (fun i j => raw21863 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21863step0 raw21863; decide +kernel
      have hl : raw21863step0Labels = raw21863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21863 raw21863Labels permutation265 hz
    mixedMoment B raw21863step0 raw21863step0Labels = mixedMoment B raw21863step1 raw21863step1Labels := by
      have ha : raw21863step1 = (fun i j => raw21863step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21863step1 raw21863step0; decide +kernel
      have hl : raw21863step1Labels = raw21863step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21863step0 raw21863step0Labels permutation38 permutation7
    mixedMoment B raw21863step1 raw21863step1Labels = mixedMoment B raw21863step2 raw21863step2Labels := by
      have ha : raw21863step2 = -raw21863step1 := by apply Matrix.ext; change ∀ i j, raw21863step2 i j = -(raw21863step1 i j); unfold raw21863step2 raw21863step1; decide +kernel
      have hl : raw21863step2Labels = raw21863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21863step2 raw21863step2Labels = mixedMoment B raw21863step3 raw21863step3Labels := by
      have ha : raw21863step3 = raw21863step2 := by apply Matrix.ext; unfold raw21863step3 raw21863step2; decide +kernel
      have hl : raw21863step2Labels = labelEmbedding1 ∘ raw21863step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21863step2 raw21863step2Labels raw21863step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

def raw21864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21864step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21864step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21864step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21864step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21864step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21864step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21864 raw21864Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw21864 raw21864Labels = mixedMoment B raw21864step0 raw21864step0Labels := by
      have hz : ∀ j, raw21864 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21864step0 = (fun i j => raw21864 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21864step0 raw21864; decide +kernel
      have hl : raw21864step0Labels = raw21864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21864 raw21864Labels permutation434 hz
    mixedMoment B raw21864step0 raw21864step0Labels = mixedMoment B raw21864step1 raw21864step1Labels := by
      have hz : ∀ j, raw21864step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21864step1 = (fun i j => raw21864step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21864step1 raw21864step0; decide +kernel
      have hl : raw21864step1Labels = raw21864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21864step0 raw21864step0Labels permutation56 hz
    mixedMoment B raw21864step1 raw21864step1Labels = mixedMoment B raw21864step2 raw21864step2Labels := by
      have ha : raw21864step2 = (fun i j => raw21864step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21864step2 raw21864step1; decide +kernel
      have hl : raw21864step2Labels = raw21864step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21864step1 raw21864step1Labels permutation8 permutation7
    mixedMoment B raw21864step2 raw21864step2Labels = mixedMoment B raw21864step3 raw21864step3Labels := by
      have ha : raw21864step3 = -raw21864step2 := by apply Matrix.ext; change ∀ i j, raw21864step3 i j = -(raw21864step2 i j); unfold raw21864step3 raw21864step2; decide +kernel
      have hl : raw21864step3Labels = raw21864step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21864step3 raw21864step3Labels = mixedMoment B raw21864step4 raw21864step4Labels := by
      have ha : raw21864step4 = raw21864step3 := by apply Matrix.ext; unfold raw21864step4 raw21864step3; decide +kernel
      have hl : raw21864step3Labels = labelEmbedding1 ∘ raw21864step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21864step3 raw21864step3Labels raw21864step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw21865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21865step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21865step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21865step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21865step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21865step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21865step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21865step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21865 raw21865Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw21865 raw21865Labels = mixedMoment B raw21865step0 raw21865step0Labels := by
      have hz : ∀ j, raw21865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21865step0 = (fun i j => raw21865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21865step0 raw21865; decide +kernel
      have hl : raw21865step0Labels = raw21865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21865 raw21865Labels permutation346 hz
    mixedMoment B raw21865step0 raw21865step0Labels = mixedMoment B raw21865step1 raw21865step1Labels := by
      have hz : ∀ j, raw21865step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21865step1 = (fun i j => raw21865step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21865step1 raw21865step0; decide +kernel
      have hl : raw21865step1Labels = raw21865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21865step0 raw21865step0Labels permutation56 hz
    mixedMoment B raw21865step1 raw21865step1Labels = mixedMoment B raw21865step2 raw21865step2Labels := by
      have ha : raw21865step2 = (fun i j => raw21865step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21865step2 raw21865step1; decide +kernel
      have hl : raw21865step2Labels = raw21865step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21865step1 raw21865step1Labels permutation8 permutation7
    mixedMoment B raw21865step2 raw21865step2Labels = mixedMoment B raw21865step3 raw21865step3Labels := by
      have ha : raw21865step3 = -raw21865step2 := by apply Matrix.ext; change ∀ i j, raw21865step3 i j = -(raw21865step2 i j); unfold raw21865step3 raw21865step2; decide +kernel
      have hl : raw21865step3Labels = raw21865step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21865step3 raw21865step3Labels = mixedMoment B raw21865step4 raw21865step4Labels := by
      have ha : raw21865step4 = raw21865step3 := by apply Matrix.ext; unfold raw21865step4 raw21865step3; decide +kernel
      have hl : raw21865step3Labels = labelEmbedding1 ∘ raw21865step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21865step3 raw21865step3Labels raw21865step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1509 node1509Labels := by rfl

def raw21866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21866step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21866step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21866step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21866 raw21866Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21866 raw21866Labels = mixedMoment B raw21866step0 raw21866step0Labels := by
      have hz : ∀ j, raw21866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21866step0 = (fun i j => raw21866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21866step0 raw21866; decide +kernel
      have hl : raw21866step0Labels = raw21866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21866 raw21866Labels permutation346 hz
    mixedMoment B raw21866step0 raw21866step0Labels = mixedMoment B raw21866step1 raw21866step1Labels := by
      have ha : raw21866step1 = (fun i j => raw21866step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21866step1 raw21866step0; decide +kernel
      have hl : raw21866step1Labels = raw21866step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21866step0 raw21866step0Labels permutation32 permutation7
    mixedMoment B raw21866step1 raw21866step1Labels = mixedMoment B raw21866step2 raw21866step2Labels := by
      have ha : raw21866step2 = -raw21866step1 := by apply Matrix.ext; change ∀ i j, raw21866step2 i j = -(raw21866step1 i j); unfold raw21866step2 raw21866step1; decide +kernel
      have hl : raw21866step2Labels = raw21866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21866step2 raw21866step2Labels = mixedMoment B raw21866step3 raw21866step3Labels := by
      have ha : raw21866step3 = raw21866step2 := by apply Matrix.ext; unfold raw21866step3 raw21866step2; decide +kernel
      have hl : raw21866step2Labels = labelEmbedding1 ∘ raw21866step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21866step2 raw21866step2Labels raw21866step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

def raw21867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21867step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw21867step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21867step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21867step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw21867step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21867 raw21867Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw21867 raw21867Labels = mixedMoment B raw21867step0 raw21867step0Labels := by
      have hz : ∀ j, raw21867 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21867step0 = (fun i j => raw21867 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21867step0 raw21867; decide +kernel
      have hl : raw21867step0Labels = raw21867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21867 raw21867Labels permutation265 hz
    mixedMoment B raw21867step0 raw21867step0Labels = mixedMoment B raw21867step1 raw21867step1Labels := by
      have ha : raw21867step1 = (fun i j => raw21867step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21867step1 raw21867step0; decide +kernel
      have hl : raw21867step1Labels = raw21867step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21867step0 raw21867step0Labels permutation32 permutation7
    mixedMoment B raw21867step1 raw21867step1Labels = mixedMoment B raw21867step2 raw21867step2Labels := by
      have ha : raw21867step2 = -raw21867step1 := by apply Matrix.ext; change ∀ i j, raw21867step2 i j = -(raw21867step1 i j); unfold raw21867step2 raw21867step1; decide +kernel
      have hl : raw21867step2Labels = raw21867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21867step2 raw21867step2Labels = mixedMoment B raw21867step3 raw21867step3Labels := by
      have ha : raw21867step3 = raw21867step2 := by apply Matrix.ext; unfold raw21867step3 raw21867step2; decide +kernel
      have hl : raw21867step2Labels = labelEmbedding1 ∘ raw21867step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21867step2 raw21867step2Labels raw21867step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

def raw21868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21868step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21868step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21868step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21868step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21868step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21868step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21868 raw21868Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw21868 raw21868Labels = mixedMoment B raw21868step0 raw21868step0Labels := by
      have hz : ∀ j, raw21868 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21868step0 = (fun i j => raw21868 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21868step0 raw21868; decide +kernel
      have hl : raw21868step0Labels = raw21868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21868 raw21868Labels permutation346 hz
    mixedMoment B raw21868step0 raw21868step0Labels = mixedMoment B raw21868step1 raw21868step1Labels := by
      have hz : ∀ j, raw21868step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21868step1 = (fun i j => raw21868step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21868step1 raw21868step0; decide +kernel
      have hl : raw21868step1Labels = raw21868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21868step0 raw21868step0Labels permutation56 hz
    mixedMoment B raw21868step1 raw21868step1Labels = mixedMoment B raw21868step2 raw21868step2Labels := by
      have ha : raw21868step2 = (fun i j => raw21868step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21868step2 raw21868step1; decide +kernel
      have hl : raw21868step2Labels = raw21868step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21868step1 raw21868step1Labels permutation8 permutation7
    mixedMoment B raw21868step2 raw21868step2Labels = mixedMoment B raw21868step3 raw21868step3Labels := by
      have ha : raw21868step3 = -raw21868step2 := by apply Matrix.ext; change ∀ i j, raw21868step3 i j = -(raw21868step2 i j); unfold raw21868step3 raw21868step2; decide +kernel
      have hl : raw21868step3Labels = raw21868step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21868step3 raw21868step3Labels = mixedMoment B raw21868step4 raw21868step4Labels := by
      have ha : raw21868step4 = raw21868step3 := by apply Matrix.ext; unfold raw21868step4 raw21868step3; decide +kernel
      have hl : raw21868step3Labels = labelEmbedding1 ∘ raw21868step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21868step3 raw21868step3Labels raw21868step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw21869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21869Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21869step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21869step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw21869step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21869step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw21869step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21869step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw21869step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21869step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw21869step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21869 raw21869Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw21869 raw21869Labels = mixedMoment B raw21869step0 raw21869step0Labels := by
      have hz : ∀ j, raw21869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21869step0 = (fun i j => raw21869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21869step0 raw21869; decide +kernel
      have hl : raw21869step0Labels = raw21869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21869 raw21869Labels permutation434 hz
    mixedMoment B raw21869step0 raw21869step0Labels = mixedMoment B raw21869step1 raw21869step1Labels := by
      have hz : ∀ j, raw21869step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21869step1 = (fun i j => raw21869step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21869step1 raw21869step0; decide +kernel
      have hl : raw21869step1Labels = raw21869step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21869step0 raw21869step0Labels permutation80 hz
    mixedMoment B raw21869step1 raw21869step1Labels = mixedMoment B raw21869step2 raw21869step2Labels := by
      have hz : ∀ j, raw21869step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21869step2 = (fun i j => raw21869step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21869step2 raw21869step1; decide +kernel
      have hl : raw21869step2Labels = raw21869step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21869step1 raw21869step1Labels permutation14 hz
    mixedMoment B raw21869step2 raw21869step2Labels = mixedMoment B raw21869step3 raw21869step3Labels := by
      have ha : raw21869step3 = (fun i j => raw21869step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21869step3 raw21869step2; decide +kernel
      have hl : raw21869step3Labels = raw21869step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21869step2 raw21869step2Labels permutation2 permutation7
    mixedMoment B raw21869step3 raw21869step3Labels = mixedMoment B raw21869step4 raw21869step4Labels := by
      have ha : raw21869step4 = -raw21869step3 := by apply Matrix.ext; change ∀ i j, raw21869step4 i j = -(raw21869step3 i j); unfold raw21869step4 raw21869step3; decide +kernel
      have hl : raw21869step4Labels = raw21869step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21869step4 raw21869step4Labels = mixedMoment B raw21869step5 raw21869step5Labels := by
      have ha : raw21869step5 = raw21869step4 := by apply Matrix.ext; unfold raw21869step5 raw21869step4; decide +kernel
      have hl : raw21869step4Labels = labelEmbedding1 ∘ raw21869step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21869step4 raw21869step4Labels raw21869step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1527 node1527Labels := by rfl

def raw21870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21870Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21870step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21870step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw21870step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21870step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21870step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21870step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21870step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21870 raw21870Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw21870 raw21870Labels = mixedMoment B raw21870step0 raw21870step0Labels := by
      have hz : ∀ j, raw21870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21870step0 = (fun i j => raw21870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21870step0 raw21870; decide +kernel
      have hl : raw21870step0Labels = raw21870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21870 raw21870Labels permutation434 hz
    mixedMoment B raw21870step0 raw21870step0Labels = mixedMoment B raw21870step1 raw21870step1Labels := by
      have hz : ∀ j, raw21870step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21870step1 = (fun i j => raw21870step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21870step1 raw21870step0; decide +kernel
      have hl : raw21870step1Labels = raw21870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21870step0 raw21870step0Labels permutation80 hz
    mixedMoment B raw21870step1 raw21870step1Labels = mixedMoment B raw21870step2 raw21870step2Labels := by
      have ha : raw21870step2 = (fun i j => raw21870step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21870step2 raw21870step1; decide +kernel
      have hl : raw21870step2Labels = raw21870step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21870step1 raw21870step1Labels permutation8 permutation7
    mixedMoment B raw21870step2 raw21870step2Labels = mixedMoment B raw21870step3 raw21870step3Labels := by
      have ha : raw21870step3 = -raw21870step2 := by apply Matrix.ext; change ∀ i j, raw21870step3 i j = -(raw21870step2 i j); unfold raw21870step3 raw21870step2; decide +kernel
      have hl : raw21870step3Labels = raw21870step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21870step3 raw21870step3Labels = mixedMoment B raw21870step4 raw21870step4Labels := by
      have ha : raw21870step4 = raw21870step3 := by apply Matrix.ext; unfold raw21870step4 raw21870step3; decide +kernel
      have hl : raw21870step3Labels = labelEmbedding1 ∘ raw21870step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21870step3 raw21870step3Labels raw21870step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

def raw21871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21871Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21871step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21871step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw21871step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21871step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21871step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21871step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21871step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21871 raw21871Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw21871 raw21871Labels = mixedMoment B raw21871step0 raw21871step0Labels := by
      have hz : ∀ j, raw21871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21871step0 = (fun i j => raw21871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21871step0 raw21871; decide +kernel
      have hl : raw21871step0Labels = raw21871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21871 raw21871Labels permutation434 hz
    mixedMoment B raw21871step0 raw21871step0Labels = mixedMoment B raw21871step1 raw21871step1Labels := by
      have hz : ∀ j, raw21871step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21871step1 = (fun i j => raw21871step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21871step1 raw21871step0; decide +kernel
      have hl : raw21871step1Labels = raw21871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21871step0 raw21871step0Labels permutation56 hz
    mixedMoment B raw21871step1 raw21871step1Labels = mixedMoment B raw21871step2 raw21871step2Labels := by
      have ha : raw21871step2 = (fun i j => raw21871step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21871step2 raw21871step1; decide +kernel
      have hl : raw21871step2Labels = raw21871step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21871step1 raw21871step1Labels permutation8 permutation7
    mixedMoment B raw21871step2 raw21871step2Labels = mixedMoment B raw21871step3 raw21871step3Labels := by
      have ha : raw21871step3 = -raw21871step2 := by apply Matrix.ext; change ∀ i j, raw21871step3 i j = -(raw21871step2 i j); unfold raw21871step3 raw21871step2; decide +kernel
      have hl : raw21871step3Labels = raw21871step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21871step3 raw21871step3Labels = mixedMoment B raw21871step4 raw21871step4Labels := by
      have ha : raw21871step4 = raw21871step3 := by apply Matrix.ext; unfold raw21871step4 raw21871step3; decide +kernel
      have hl : raw21871step3Labels = labelEmbedding1 ∘ raw21871step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21871step3 raw21871step3Labels raw21871step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

def raw21872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21872Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21872step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21872step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw21872step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21872step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21872step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21872step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw21872step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21872 raw21872Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw21872 raw21872Labels = mixedMoment B raw21872step0 raw21872step0Labels := by
      have hz : ∀ j, raw21872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21872step0 = (fun i j => raw21872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21872step0 raw21872; decide +kernel
      have hl : raw21872step0Labels = raw21872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21872 raw21872Labels permutation346 hz
    mixedMoment B raw21872step0 raw21872step0Labels = mixedMoment B raw21872step1 raw21872step1Labels := by
      have hz : ∀ j, raw21872step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21872step1 = (fun i j => raw21872step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21872step1 raw21872step0; decide +kernel
      have hl : raw21872step1Labels = raw21872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21872step0 raw21872step0Labels permutation56 hz
    mixedMoment B raw21872step1 raw21872step1Labels = mixedMoment B raw21872step2 raw21872step2Labels := by
      have ha : raw21872step2 = (fun i j => raw21872step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21872step2 raw21872step1; decide +kernel
      have hl : raw21872step2Labels = raw21872step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21872step1 raw21872step1Labels permutation8 permutation7
    mixedMoment B raw21872step2 raw21872step2Labels = mixedMoment B raw21872step3 raw21872step3Labels := by
      have ha : raw21872step3 = -raw21872step2 := by apply Matrix.ext; change ∀ i j, raw21872step3 i j = -(raw21872step2 i j); unfold raw21872step3 raw21872step2; decide +kernel
      have hl : raw21872step3Labels = raw21872step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21872step3 raw21872step3Labels = mixedMoment B raw21872step4 raw21872step4Labels := by
      have ha : raw21872step4 = raw21872step3 := by apply Matrix.ext; unfold raw21872step4 raw21872step3; decide +kernel
      have hl : raw21872step3Labels = labelEmbedding1 ∘ raw21872step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21872step3 raw21872step3Labels raw21872step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

def raw21873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21873step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw21873step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw21873step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21873step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw21873step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21873step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw21873step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21873step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw21873step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21873 raw21873Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw21873 raw21873Labels = mixedMoment B raw21873step0 raw21873step0Labels := by
      have hz : ∀ j, raw21873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21873step0 = (fun i j => raw21873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21873step0 raw21873; decide +kernel
      have hl : raw21873step0Labels = raw21873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21873 raw21873Labels permutation434 hz
    mixedMoment B raw21873step0 raw21873step0Labels = mixedMoment B raw21873step1 raw21873step1Labels := by
      have hz : ∀ j, raw21873step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21873step1 = (fun i j => raw21873step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21873step1 raw21873step0; decide +kernel
      have hl : raw21873step1Labels = raw21873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21873step0 raw21873step0Labels permutation80 hz
    mixedMoment B raw21873step1 raw21873step1Labels = mixedMoment B raw21873step2 raw21873step2Labels := by
      have hz : ∀ j, raw21873step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21873step2 = (fun i j => raw21873step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21873step2 raw21873step1; decide +kernel
      have hl : raw21873step2Labels = raw21873step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21873step1 raw21873step1Labels permutation14 hz
    mixedMoment B raw21873step2 raw21873step2Labels = mixedMoment B raw21873step3 raw21873step3Labels := by
      have ha : raw21873step3 = (fun i j => raw21873step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21873step3 raw21873step2; decide +kernel
      have hl : raw21873step3Labels = raw21873step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21873step2 raw21873step2Labels permutation2 permutation7
    mixedMoment B raw21873step3 raw21873step3Labels = mixedMoment B raw21873step4 raw21873step4Labels := by
      have ha : raw21873step4 = -raw21873step3 := by apply Matrix.ext; change ∀ i j, raw21873step4 i j = -(raw21873step3 i j); unfold raw21873step4 raw21873step3; decide +kernel
      have hl : raw21873step4Labels = raw21873step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21873step4 raw21873step4Labels = mixedMoment B raw21873step5 raw21873step5Labels := by
      have ha : raw21873step5 = raw21873step4 := by apply Matrix.ext; unfold raw21873step5 raw21873step4; decide +kernel
      have hl : raw21873step4Labels = labelEmbedding1 ∘ raw21873step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21873step4 raw21873step4Labels raw21873step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

def raw21874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21874step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw21874step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![4, -1, -3]]
def raw21874step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw21874step3Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21874step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def raw21874step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21874step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def raw21874step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21874 raw21874Labels = mixedMoment B node1758 node1758Labels := by
  calc
    mixedMoment B raw21874 raw21874Labels = mixedMoment B raw21874step0 raw21874step0Labels := by
      have hz : ∀ j, raw21874 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21874step0 = (fun i j => raw21874 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21874step0 raw21874; decide +kernel
      have hl : raw21874step0Labels = raw21874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21874 raw21874Labels permutation520 hz
    mixedMoment B raw21874step0 raw21874step0Labels = mixedMoment B raw21874step1 raw21874step1Labels := by
      have hz : ∀ j, raw21874step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21874step1 = (fun i j => raw21874step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21874step1 raw21874step0; decide +kernel
      have hl : raw21874step1Labels = raw21874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21874step0 raw21874step0Labels permutation104 hz
    mixedMoment B raw21874step1 raw21874step1Labels = mixedMoment B raw21874step2 raw21874step2Labels := by
      have hz : ∀ j, raw21874step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21874step2 = (fun i j => raw21874step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21874step2 raw21874step1; decide +kernel
      have hl : raw21874step2Labels = raw21874step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21874step1 raw21874step1Labels permutation20 hz
    mixedMoment B raw21874step2 raw21874step2Labels = mixedMoment B raw21874step3 raw21874step3Labels := by
      have hz : ∀ j, raw21874step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw21874step3 = (fun i j => raw21874step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw21874step3 raw21874step2; decide +kernel
      have hl : raw21874step3Labels = raw21874step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21874step2 raw21874step2Labels permutation4 hz
    mixedMoment B raw21874step3 raw21874step3Labels = mixedMoment B raw21874step4 raw21874step4Labels := by
      have ha : raw21874step4 = (fun i j => raw21874step3 (permutation1 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21874step4 raw21874step3; decide +kernel
      have hl : raw21874step4Labels = raw21874step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21874step3 raw21874step3Labels permutation1 permutation7
    mixedMoment B raw21874step4 raw21874step4Labels = mixedMoment B raw21874step5 raw21874step5Labels := by
      have ha : raw21874step5 = raw21874step4 := by apply Matrix.ext; unfold raw21874step5 raw21874step4; decide +kernel
      have hl : raw21874step4Labels = labelEmbedding1 ∘ raw21874step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21874step4 raw21874step4Labels raw21874step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1758 node1758Labels := by rfl

def raw21875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21875step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw21875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21875 raw21875Labels = mixedMoment B node1085 node1085Labels := by
  calc
    mixedMoment B raw21875 raw21875Labels = mixedMoment B raw21875step0 raw21875step0Labels := by
      have hz : ∀ j, raw21875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21875step0 = (fun i j => raw21875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21875step0 raw21875; decide +kernel
      have hl : raw21875step0Labels = raw21875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21875 raw21875Labels permutation434 hz
    mixedMoment B raw21875step0 raw21875step0Labels = mixedMoment B raw21875step1 raw21875step1Labels := by
      have hz : ∀ j, raw21875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21875step1 = (fun i j => raw21875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21875step1 raw21875step0; decide +kernel
      have hl : raw21875step1Labels = raw21875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21875step0 raw21875step0Labels permutation80 hz
    mixedMoment B raw21875step1 raw21875step1Labels = mixedMoment B raw21875step2 raw21875step2Labels := by
      have hz : ∀ j, raw21875step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21875step2 = (fun i j => raw21875step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21875step2 raw21875step1; decide +kernel
      have hl : raw21875step2Labels = raw21875step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21875step1 raw21875step1Labels permutation14 hz
    _ = mixedMoment B node1085 node1085Labels := by rfl

def raw21876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21876 raw21876Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw21876 raw21876Labels = mixedMoment B raw21876step0 raw21876step0Labels := by
      have hz : ∀ j, raw21876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21876step0 = (fun i j => raw21876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21876step0 raw21876; decide +kernel
      have hl : raw21876step0Labels = raw21876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21876 raw21876Labels permutation434 hz
    mixedMoment B raw21876step0 raw21876step0Labels = mixedMoment B raw21876step1 raw21876step1Labels := by
      have hz : ∀ j, raw21876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21876step1 = (fun i j => raw21876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21876step1 raw21876step0; decide +kernel
      have hl : raw21876step1Labels = raw21876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21876step0 raw21876step0Labels permutation80 hz
    _ = mixedMoment B node602 node602Labels := by rfl

def raw21877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21877 raw21877Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw21877 raw21877Labels = mixedMoment B raw21877step0 raw21877step0Labels := by
      have hz : ∀ j, raw21877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21877step0 = (fun i j => raw21877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21877step0 raw21877; decide +kernel
      have hl : raw21877step0Labels = raw21877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21877 raw21877Labels permutation434 hz
    mixedMoment B raw21877step0 raw21877step0Labels = mixedMoment B raw21877step1 raw21877step1Labels := by
      have hz : ∀ j, raw21877step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21877step1 = (fun i j => raw21877step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21877step1 raw21877step0; decide +kernel
      have hl : raw21877step1Labels = raw21877step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21877step0 raw21877step0Labels permutation56 hz
    _ = mixedMoment B node602 node602Labels := by rfl

def raw21878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21878 raw21878Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw21878 raw21878Labels = mixedMoment B raw21878step0 raw21878step0Labels := by
      have hz : ∀ j, raw21878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21878step0 = (fun i j => raw21878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21878step0 raw21878; decide +kernel
      have hl : raw21878step0Labels = raw21878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21878 raw21878Labels permutation346 hz
    mixedMoment B raw21878step0 raw21878step0Labels = mixedMoment B raw21878step1 raw21878step1Labels := by
      have hz : ∀ j, raw21878step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21878step1 = (fun i j => raw21878step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21878step1 raw21878step0; decide +kernel
      have hl : raw21878step1Labels = raw21878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21878step0 raw21878step0Labels permutation56 hz
    _ = mixedMoment B node602 node602Labels := by rfl

def raw21879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw21879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21879step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw21879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21879 raw21879Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw21879 raw21879Labels = mixedMoment B raw21879step0 raw21879step0Labels := by
      have hz : ∀ j, raw21879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21879step0 = (fun i j => raw21879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21879step0 raw21879; decide +kernel
      have hl : raw21879step0Labels = raw21879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21879 raw21879Labels permutation434 hz
    mixedMoment B raw21879step0 raw21879step0Labels = mixedMoment B raw21879step1 raw21879step1Labels := by
      have hz : ∀ j, raw21879step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21879step1 = (fun i j => raw21879step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21879step1 raw21879step0; decide +kernel
      have hl : raw21879step1Labels = raw21879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21879step0 raw21879step0Labels permutation80 hz
    mixedMoment B raw21879step1 raw21879step1Labels = mixedMoment B raw21879step2 raw21879step2Labels := by
      have hz : ∀ j, raw21879step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21879step2 = (fun i j => raw21879step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21879step2 raw21879step1; decide +kernel
      have hl : raw21879step2Labels = raw21879step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21879step1 raw21879step1Labels permutation14 hz
    _ = mixedMoment B node618 node618Labels := by rfl

def raw21880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21880 raw21880Labels = mixedMoment B node921 node921Labels := by
  calc
    mixedMoment B raw21880 raw21880Labels = mixedMoment B raw21880step0 raw21880step0Labels := by
      have hz : ∀ j, raw21880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21880step0 = (fun i j => raw21880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21880step0 raw21880; decide +kernel
      have hl : raw21880step0Labels = raw21880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21880 raw21880Labels permutation434 hz
    mixedMoment B raw21880step0 raw21880step0Labels = mixedMoment B raw21880step1 raw21880step1Labels := by
      have ha : raw21880step1 = (fun i j => raw21880step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21880step1 raw21880step0; decide +kernel
      have hl : raw21880step1Labels = raw21880step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21880step0 raw21880step0Labels permutation38 permutation2
    _ = mixedMoment B node921 node921Labels := by rfl

def raw21881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21881 raw21881Labels = mixedMoment B node921 node921Labels := by
  calc
    mixedMoment B raw21881 raw21881Labels = mixedMoment B raw21881step0 raw21881step0Labels := by
      have hz : ∀ j, raw21881 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21881step0 = (fun i j => raw21881 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21881step0 raw21881; decide +kernel
      have hl : raw21881step0Labels = raw21881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21881 raw21881Labels permutation346 hz
    mixedMoment B raw21881step0 raw21881step0Labels = mixedMoment B raw21881step1 raw21881step1Labels := by
      have ha : raw21881step1 = (fun i j => raw21881step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21881step1 raw21881step0; decide +kernel
      have hl : raw21881step1Labels = raw21881step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21881step0 raw21881step0Labels permutation38 permutation2
    _ = mixedMoment B node921 node921Labels := by rfl

def raw21882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw21882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw21882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw21882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21882step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw21882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21882 raw21882Labels = mixedMoment B node1085 node1085Labels := by
  calc
    mixedMoment B raw21882 raw21882Labels = mixedMoment B raw21882step0 raw21882step0Labels := by
      have hz : ∀ j, raw21882 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21882step0 = (fun i j => raw21882 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21882step0 raw21882; decide +kernel
      have hl : raw21882step0Labels = raw21882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21882 raw21882Labels permutation520 hz
    mixedMoment B raw21882step0 raw21882step0Labels = mixedMoment B raw21882step1 raw21882step1Labels := by
      have hz : ∀ j, raw21882step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21882step1 = (fun i j => raw21882step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21882step1 raw21882step0; decide +kernel
      have hl : raw21882step1Labels = raw21882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21882step0 raw21882step0Labels permutation104 hz
    mixedMoment B raw21882step1 raw21882step1Labels = mixedMoment B raw21882step2 raw21882step2Labels := by
      have hz : ∀ j, raw21882step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21882step2 = (fun i j => raw21882step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21882step2 raw21882step1; decide +kernel
      have hl : raw21882step2Labels = raw21882step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21882step1 raw21882step1Labels permutation20 hz
    _ = mixedMoment B node1085 node1085Labels := by rfl

def raw21883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21883 raw21883Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw21883 raw21883Labels = mixedMoment B raw21883step0 raw21883step0Labels := by
      have hz : ∀ j, raw21883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21883step0 = (fun i j => raw21883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21883step0 raw21883; decide +kernel
      have hl : raw21883step0Labels = raw21883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21883 raw21883Labels permutation434 hz
    mixedMoment B raw21883step0 raw21883step0Labels = mixedMoment B raw21883step1 raw21883step1Labels := by
      have hz : ∀ j, raw21883step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21883step1 = (fun i j => raw21883step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21883step1 raw21883step0; decide +kernel
      have hl : raw21883step1Labels = raw21883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21883step0 raw21883step0Labels permutation80 hz
    _ = mixedMoment B node1080 node1080Labels := by rfl

def raw21884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21884 raw21884Labels = mixedMoment B node1010 node1010Labels := by
  calc
    mixedMoment B raw21884 raw21884Labels = mixedMoment B raw21884step0 raw21884step0Labels := by
      have hz : ∀ j, raw21884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21884step0 = (fun i j => raw21884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21884step0 raw21884; decide +kernel
      have hl : raw21884step0Labels = raw21884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21884 raw21884Labels permutation346 hz
    mixedMoment B raw21884step0 raw21884step0Labels = mixedMoment B raw21884step1 raw21884step1Labels := by
      have hz : ∀ j, raw21884step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21884step1 = (fun i j => raw21884step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21884step1 raw21884step0; decide +kernel
      have hl : raw21884step1Labels = raw21884step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21884step0 raw21884step0Labels permutation56 hz
    _ = mixedMoment B node1010 node1010Labels := by rfl

def raw21885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21885 raw21885Labels = mixedMoment B node2004 node2004Labels := by
  calc
    mixedMoment B raw21885 raw21885Labels = mixedMoment B raw21885step0 raw21885step0Labels := by
      have hz : ∀ j, raw21885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21885step0 = (fun i j => raw21885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21885step0 raw21885; decide +kernel
      have hl : raw21885step0Labels = raw21885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21885 raw21885Labels permutation346 hz
    _ = mixedMoment B node2004 node2004Labels := by rfl

def raw21886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21886 raw21886Labels = mixedMoment B node2004 node2004Labels := by
  calc
    mixedMoment B raw21886 raw21886Labels = mixedMoment B raw21886step0 raw21886step0Labels := by
      have hz : ∀ j, raw21886 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21886step0 = (fun i j => raw21886 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21886step0 raw21886; decide +kernel
      have hl : raw21886step0Labels = raw21886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21886 raw21886Labels permutation265 hz
    _ = mixedMoment B node2004 node2004Labels := by rfl

def raw21887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw21887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21887 raw21887Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw21887 raw21887Labels = mixedMoment B raw21887step0 raw21887step0Labels := by
      have hz : ∀ j, raw21887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21887step0 = (fun i j => raw21887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21887step0 raw21887; decide +kernel
      have hl : raw21887step0Labels = raw21887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21887 raw21887Labels permutation346 hz
    mixedMoment B raw21887step0 raw21887step0Labels = mixedMoment B raw21887step1 raw21887step1Labels := by
      have hz : ∀ j, raw21887step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21887step1 = (fun i j => raw21887step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21887step1 raw21887step0; decide +kernel
      have hl : raw21887step1Labels = raw21887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21887step0 raw21887step0Labels permutation56 hz
    _ = mixedMoment B node1951 node1951Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
