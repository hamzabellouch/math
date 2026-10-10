import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw3712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3712 raw3712Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw3712 raw3712Labels = mixedMoment B raw3712step0 raw3712step0Labels := by
      have hz : ∀ j, raw3712 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3712step0 = (fun i j => raw3712 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3712step0 raw3712; decide +kernel
      have hl : raw3712step0Labels = raw3712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3712 raw3712Labels permutation265 hz
    mixedMoment B raw3712step0 raw3712step0Labels = mixedMoment B raw3712step1 raw3712step1Labels := by
      have ha : raw3712step1 = (fun i j => raw3712step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3712step1 raw3712step0; decide +kernel
      have hl : raw3712step1Labels = raw3712step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3712step0 raw3712step0Labels permutation32 permutation6
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw3713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3713step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -1, 3]]
def raw3713step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3713 raw3713Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw3713 raw3713Labels = mixedMoment B raw3713step0 raw3713step0Labels := by
      have hz : ∀ j, raw3713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3713step0 = (fun i j => raw3713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3713step0 raw3713; decide +kernel
      have hl : raw3713step0Labels = raw3713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3713 raw3713Labels permutation434 hz
    mixedMoment B raw3713step0 raw3713step0Labels = mixedMoment B raw3713step1 raw3713step1Labels := by
      have hz : ∀ j, raw3713step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3713step1 = (fun i j => raw3713step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3713step1 raw3713step0; decide +kernel
      have hl : raw3713step1Labels = raw3713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3713step0 raw3713step0Labels permutation80 hz
    mixedMoment B raw3713step1 raw3713step1Labels = mixedMoment B raw3713step2 raw3713step2Labels := by
      have hz : ∀ j, raw3713step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3713step2 = (fun i j => raw3713step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3713step2 raw3713step1; decide +kernel
      have hl : raw3713step2Labels = raw3713step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3713step1 raw3713step1Labels permutation14 hz
    mixedMoment B raw3713step2 raw3713step2Labels = mixedMoment B raw3713step3 raw3713step3Labels := by
      have ha : raw3713step3 = (fun i j => raw3713step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3713step3 raw3713step2; decide +kernel
      have hl : raw3713step3Labels = raw3713step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3713step2 raw3713step2Labels permutation2 permutation6
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw3714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3714step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3714step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3714 raw3714Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw3714 raw3714Labels = mixedMoment B raw3714step0 raw3714step0Labels := by
      have hz : ∀ j, raw3714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3714step0 = (fun i j => raw3714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3714step0 raw3714; decide +kernel
      have hl : raw3714step0Labels = raw3714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3714 raw3714Labels permutation346 hz
    mixedMoment B raw3714step0 raw3714step0Labels = mixedMoment B raw3714step1 raw3714step1Labels := by
      have hz : ∀ j, raw3714step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3714step1 = (fun i j => raw3714step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3714step1 raw3714step0; decide +kernel
      have hl : raw3714step1Labels = raw3714step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3714step0 raw3714step0Labels permutation56 hz
    mixedMoment B raw3714step1 raw3714step1Labels = mixedMoment B raw3714step2 raw3714step2Labels := by
      have ha : raw3714step2 = (fun i j => raw3714step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3714step2 raw3714step1; decide +kernel
      have hl : raw3714step2Labels = raw3714step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3714step1 raw3714step1Labels permutation8 permutation6
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw3715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3715 raw3715Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw3715 raw3715Labels = mixedMoment B raw3715step0 raw3715step0Labels := by
      have hz : ∀ j, raw3715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3715step0 = (fun i j => raw3715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3715step0 raw3715; decide +kernel
      have hl : raw3715step0Labels = raw3715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3715 raw3715Labels permutation346 hz
    mixedMoment B raw3715step0 raw3715step0Labels = mixedMoment B raw3715step1 raw3715step1Labels := by
      have hz : ∀ j, raw3715step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3715step1 = (fun i j => raw3715step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3715step1 raw3715step0; decide +kernel
      have hl : raw3715step1Labels = raw3715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3715step0 raw3715step0Labels permutation56 hz
    mixedMoment B raw3715step1 raw3715step1Labels = mixedMoment B raw3715step2 raw3715step2Labels := by
      have ha : raw3715step2 = (fun i j => raw3715step1 (permutation26 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3715step2 raw3715step1; decide +kernel
      have hl : raw3715step2Labels = raw3715step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3715step1 raw3715step1Labels permutation26 permutation2
    _ = mixedMoment B node2284 node2284Labels := by rfl

def raw3716 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3716step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3716 raw3716Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw3716 raw3716Labels = mixedMoment B raw3716step0 raw3716step0Labels := by
      have hz : ∀ j, raw3716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3716step0 = (fun i j => raw3716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3716step0 raw3716; decide +kernel
      have hl : raw3716step0Labels = raw3716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3716 raw3716Labels permutation346 hz
    mixedMoment B raw3716step0 raw3716step0Labels = mixedMoment B raw3716step1 raw3716step1Labels := by
      have ha : raw3716step1 = (fun i j => raw3716step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3716step1 raw3716step0; decide +kernel
      have hl : raw3716step1Labels = raw3716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3716step0 raw3716step0Labels permutation136 permutation2
    _ = mixedMoment B node2055 node2055Labels := by rfl

def raw3717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3717 raw3717Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw3717 raw3717Labels = mixedMoment B raw3717step0 raw3717step0Labels := by
      have hz : ∀ j, raw3717 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3717step0 = (fun i j => raw3717 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3717step0 raw3717; decide +kernel
      have hl : raw3717step0Labels = raw3717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3717 raw3717Labels permutation265 hz
    mixedMoment B raw3717step0 raw3717step0Labels = mixedMoment B raw3717step1 raw3717step1Labels := by
      have ha : raw3717step1 = (fun i j => raw3717step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3717step1 raw3717step0; decide +kernel
      have hl : raw3717step1Labels = raw3717step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3717step0 raw3717step0Labels permutation136 permutation2
    _ = mixedMoment B node2055 node2055Labels := by rfl

def raw3718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw3718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw3718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3718 raw3718Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw3718 raw3718Labels = mixedMoment B raw3718step0 raw3718step0Labels := by
      have hz : ∀ j, raw3718 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3718step0 = (fun i j => raw3718 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3718step0 raw3718; decide +kernel
      have hl : raw3718step0Labels = raw3718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718 raw3718Labels permutation434 hz
    mixedMoment B raw3718step0 raw3718step0Labels = mixedMoment B raw3718step1 raw3718step1Labels := by
      have hz : ∀ j, raw3718step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3718step1 = (fun i j => raw3718step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3718step1 raw3718step0; decide +kernel
      have hl : raw3718step1Labels = raw3718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718step0 raw3718step0Labels permutation80 hz
    mixedMoment B raw3718step1 raw3718step1Labels = mixedMoment B raw3718step2 raw3718step2Labels := by
      have hz : ∀ j, raw3718step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3718step2 = (fun i j => raw3718step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3718step2 raw3718step1; decide +kernel
      have hl : raw3718step2Labels = raw3718step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718step1 raw3718step1Labels permutation14 hz
    mixedMoment B raw3718step2 raw3718step2Labels = mixedMoment B raw3718step3 raw3718step3Labels := by
      have ha : raw3718step3 = (fun i j => raw3718step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3718step3 raw3718step2; decide +kernel
      have hl : raw3718step3Labels = raw3718step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3718step2 raw3718step2Labels permutation6 permutation2
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw3719 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3719Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3719step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3719 raw3719Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw3719 raw3719Labels = mixedMoment B raw3719step0 raw3719step0Labels := by
      have hz : ∀ j, raw3719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3719step0 = (fun i j => raw3719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3719step0 raw3719; decide +kernel
      have hl : raw3719step0Labels = raw3719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3719 raw3719Labels permutation346 hz
    mixedMoment B raw3719step0 raw3719step0Labels = mixedMoment B raw3719step1 raw3719step1Labels := by
      have hz : ∀ j, raw3719step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3719step1 = (fun i j => raw3719step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3719step1 raw3719step0; decide +kernel
      have hl : raw3719step1Labels = raw3719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3719step0 raw3719step0Labels permutation56 hz
    mixedMoment B raw3719step1 raw3719step1Labels = mixedMoment B raw3719step2 raw3719step2Labels := by
      have ha : raw3719step2 = (fun i j => raw3719step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3719step2 raw3719step1; decide +kernel
      have hl : raw3719step2Labels = raw3719step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3719step1 raw3719step1Labels permutation29 permutation2
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw3720 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3720step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3720 raw3720Labels = mixedMoment B node1084 node1084Labels := by
  calc
    mixedMoment B raw3720 raw3720Labels = mixedMoment B raw3720step0 raw3720step0Labels := by
      have hz : ∀ j, raw3720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3720step0 = (fun i j => raw3720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3720step0 raw3720; decide +kernel
      have hl : raw3720step0Labels = raw3720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3720 raw3720Labels permutation346 hz
    mixedMoment B raw3720step0 raw3720step0Labels = mixedMoment B raw3720step1 raw3720step1Labels := by
      have hz : ∀ j, raw3720step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3720step1 = (fun i j => raw3720step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3720step1 raw3720step0; decide +kernel
      have hl : raw3720step1Labels = raw3720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3720step0 raw3720step0Labels permutation56 hz
    mixedMoment B raw3720step1 raw3720step1Labels = mixedMoment B raw3720step2 raw3720step2Labels := by
      have ha : raw3720step2 = (fun i j => raw3720step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3720step2 raw3720step1; decide +kernel
      have hl : raw3720step2Labels = raw3720step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3720step1 raw3720step1Labels permutation28 permutation2
    _ = mixedMoment B node1084 node1084Labels := by rfl

def raw3721 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-3, 3]]
def raw3721Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![0, 0], ![-3, 3]]
def raw3721step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![-3, 3]]
def raw3721step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![-3, 3]]
def raw3721step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![3, -3], ![-3, 3]]
def raw3721step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw3721step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3721 raw3721Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3721 raw3721Labels = mixedMoment B raw3721step0 raw3721step0Labels := by
      have hz : ∀ j, raw3721 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3721step0 = (fun i j => raw3721 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3721step0 raw3721; decide +kernel
      have hl : raw3721step0Labels = raw3721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721 raw3721Labels permutation520 hz
    mixedMoment B raw3721step0 raw3721step0Labels = mixedMoment B raw3721step1 raw3721step1Labels := by
      have hz : ∀ j, raw3721step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3721step1 = (fun i j => raw3721step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3721step1 raw3721step0; decide +kernel
      have hl : raw3721step1Labels = raw3721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step0 raw3721step0Labels permutation104 hz
    mixedMoment B raw3721step1 raw3721step1Labels = mixedMoment B raw3721step2 raw3721step2Labels := by
      have hz : ∀ j, raw3721step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3721step2 = (fun i j => raw3721step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3721step2 raw3721step1; decide +kernel
      have hl : raw3721step2Labels = raw3721step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step1 raw3721step1Labels permutation20 hz
    mixedMoment B raw3721step2 raw3721step2Labels = mixedMoment B raw3721step3 raw3721step3Labels := by
      have hz : ∀ j, raw3721step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3721step3 = (fun i j => raw3721step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3721step3 raw3721step2; decide +kernel
      have hl : raw3721step3Labels = raw3721step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step2 raw3721step2Labels permutation4 hz
    mixedMoment B raw3721step3 raw3721step3Labels = mixedMoment B raw3721step4 raw3721step4Labels := by
      have ha : raw3721step4 = (fun i j => raw3721step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3721step4 raw3721step3; decide +kernel
      have hl : raw3721step4Labels = raw3721step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3721step3 raw3721step3Labels permutation1 permutation0
    _ = mixedMoment B node4085 node4085Labels := by rfl

def raw3722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3722step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3722 raw3722Labels = mixedMoment B node1066 node1066Labels := by
  calc
    mixedMoment B raw3722 raw3722Labels = mixedMoment B raw3722step0 raw3722step0Labels := by
      have hz : ∀ j, raw3722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3722step0 = (fun i j => raw3722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3722step0 raw3722; decide +kernel
      have hl : raw3722step0Labels = raw3722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3722 raw3722Labels permutation346 hz
    mixedMoment B raw3722step0 raw3722step0Labels = mixedMoment B raw3722step1 raw3722step1Labels := by
      have ha : raw3722step1 = (fun i j => raw3722step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3722step1 raw3722step0; decide +kernel
      have hl : raw3722step1Labels = raw3722step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3722step0 raw3722step0Labels permutation50 permutation4
    mixedMoment B raw3722step1 raw3722step1Labels = mixedMoment B raw3722step2 raw3722step2Labels := by
      have ha : raw3722step2 = -raw3722step1 := by apply Matrix.ext; change ∀ i j, raw3722step2 i j = -(raw3722step1 i j); unfold raw3722step2 raw3722step1; decide +kernel
      have hl : raw3722step2Labels = raw3722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1066 node1066Labels := by rfl

def raw3723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3723 raw3723Labels = mixedMoment B node1066 node1066Labels := by
  calc
    mixedMoment B raw3723 raw3723Labels = mixedMoment B raw3723step0 raw3723step0Labels := by
      have hz : ∀ j, raw3723 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3723step0 = (fun i j => raw3723 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3723step0 raw3723; decide +kernel
      have hl : raw3723step0Labels = raw3723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3723 raw3723Labels permutation265 hz
    mixedMoment B raw3723step0 raw3723step0Labels = mixedMoment B raw3723step1 raw3723step1Labels := by
      have ha : raw3723step1 = (fun i j => raw3723step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3723step1 raw3723step0; decide +kernel
      have hl : raw3723step1Labels = raw3723step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3723step0 raw3723step0Labels permutation50 permutation4
    mixedMoment B raw3723step1 raw3723step1Labels = mixedMoment B raw3723step2 raw3723step2Labels := by
      have ha : raw3723step2 = -raw3723step1 := by apply Matrix.ext; change ∀ i j, raw3723step2 i j = -(raw3723step1 i j); unfold raw3723step2 raw3723step1; decide +kernel
      have hl : raw3723step2Labels = raw3723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1066 node1066Labels := by rfl

def raw3724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-2, 2, 0], ![-2, 2, 0]]
def raw3724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3724 raw3724Labels = mixedMoment B node1068 node1068Labels := by
  calc
    mixedMoment B raw3724 raw3724Labels = mixedMoment B raw3724step0 raw3724step0Labels := by
      have hz : ∀ j, raw3724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3724step0 = (fun i j => raw3724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3724step0 raw3724; decide +kernel
      have hl : raw3724step0Labels = raw3724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3724 raw3724Labels permutation346 hz
    mixedMoment B raw3724step0 raw3724step0Labels = mixedMoment B raw3724step1 raw3724step1Labels := by
      have hz : ∀ j, raw3724step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3724step1 = (fun i j => raw3724step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3724step1 raw3724step0; decide +kernel
      have hl : raw3724step1Labels = raw3724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3724step0 raw3724step0Labels permutation56 hz
    mixedMoment B raw3724step1 raw3724step1Labels = mixedMoment B raw3724step2 raw3724step2Labels := by
      have ha : raw3724step2 = (fun i j => raw3724step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3724step2 raw3724step1; decide +kernel
      have hl : raw3724step2Labels = raw3724step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3724step1 raw3724step1Labels permutation12 permutation4
    mixedMoment B raw3724step2 raw3724step2Labels = mixedMoment B raw3724step3 raw3724step3Labels := by
      have ha : raw3724step3 = -raw3724step2 := by apply Matrix.ext; change ∀ i j, raw3724step3 i j = -(raw3724step2 i j); unfold raw3724step3 raw3724step2; decide +kernel
      have hl : raw3724step3Labels = raw3724step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1068 node1068Labels := by rfl

def raw3725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-3, 3, 0]]
def raw3725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3725 raw3725Labels = mixedMoment B node1067 node1067Labels := by
  calc
    mixedMoment B raw3725 raw3725Labels = mixedMoment B raw3725step0 raw3725step0Labels := by
      have hz : ∀ j, raw3725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3725step0 = (fun i j => raw3725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3725step0 raw3725; decide +kernel
      have hl : raw3725step0Labels = raw3725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3725 raw3725Labels permutation346 hz
    mixedMoment B raw3725step0 raw3725step0Labels = mixedMoment B raw3725step1 raw3725step1Labels := by
      have hz : ∀ j, raw3725step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3725step1 = (fun i j => raw3725step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3725step1 raw3725step0; decide +kernel
      have hl : raw3725step1Labels = raw3725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3725step0 raw3725step0Labels permutation56 hz
    mixedMoment B raw3725step1 raw3725step1Labels = mixedMoment B raw3725step2 raw3725step2Labels := by
      have ha : raw3725step2 = (fun i j => raw3725step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3725step2 raw3725step1; decide +kernel
      have hl : raw3725step2Labels = raw3725step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3725step1 raw3725step1Labels permutation12 permutation4
    mixedMoment B raw3725step2 raw3725step2Labels = mixedMoment B raw3725step3 raw3725step3Labels := by
      have ha : raw3725step3 = -raw3725step2 := by apply Matrix.ext; change ∀ i j, raw3725step3 i j = -(raw3725step2 i j); unfold raw3725step3 raw3725step2; decide +kernel
      have hl : raw3725step3Labels = raw3725step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1067 node1067Labels := by rfl

def raw3726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw3726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3726 raw3726Labels = mixedMoment B node1084 node1084Labels := by
  calc
    mixedMoment B raw3726 raw3726Labels = mixedMoment B raw3726step0 raw3726step0Labels := by
      have hz : ∀ j, raw3726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3726step0 = (fun i j => raw3726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3726step0 raw3726; decide +kernel
      have hl : raw3726step0Labels = raw3726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3726 raw3726Labels permutation346 hz
    mixedMoment B raw3726step0 raw3726step0Labels = mixedMoment B raw3726step1 raw3726step1Labels := by
      have hz : ∀ j, raw3726step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3726step1 = (fun i j => raw3726step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3726step1 raw3726step0; decide +kernel
      have hl : raw3726step1Labels = raw3726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3726step0 raw3726step0Labels permutation56 hz
    mixedMoment B raw3726step1 raw3726step1Labels = mixedMoment B raw3726step2 raw3726step2Labels := by
      have ha : raw3726step2 = (fun i j => raw3726step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3726step2 raw3726step1; decide +kernel
      have hl : raw3726step2Labels = raw3726step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3726step1 raw3726step1Labels permutation9 permutation4
    mixedMoment B raw3726step2 raw3726step2Labels = mixedMoment B raw3726step3 raw3726step3Labels := by
      have ha : raw3726step3 = -raw3726step2 := by apply Matrix.ext; change ∀ i j, raw3726step3 i j = -(raw3726step2 i j); unfold raw3726step3 raw3726step2; decide +kernel
      have hl : raw3726step3Labels = raw3726step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1084 node1084Labels := by rfl

def raw3727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3727 raw3727Labels = mixedMoment B node2040 node2040Labels := by
  calc
    mixedMoment B raw3727 raw3727Labels = mixedMoment B raw3727step0 raw3727step0Labels := by
      have ha : raw3727step0 = (fun i j => raw3727 (permutation623 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3727step0 raw3727; decide +kernel
      have hl : raw3727step0Labels = raw3727Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3727 raw3727Labels permutation623 permutation2
    _ = mixedMoment B node2040 node2040Labels := by rfl

def raw3728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3728 raw3728Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw3728 raw3728Labels = mixedMoment B raw3728step0 raw3728step0Labels := by
      have hz : ∀ j, raw3728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3728step0 = (fun i j => raw3728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3728step0 raw3728; decide +kernel
      have hl : raw3728step0Labels = raw3728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3728 raw3728Labels permutation434 hz
    mixedMoment B raw3728step0 raw3728step0Labels = mixedMoment B raw3728step1 raw3728step1Labels := by
      have hz : ∀ j, raw3728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3728step1 = (fun i j => raw3728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3728step1 raw3728step0; decide +kernel
      have hl : raw3728step1Labels = raw3728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3728step0 raw3728step0Labels permutation80 hz
    mixedMoment B raw3728step1 raw3728step1Labels = mixedMoment B raw3728step2 raw3728step2Labels := by
      have ha : raw3728step2 = (fun i j => raw3728step1 (permutation26 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3728step2 raw3728step1; decide +kernel
      have hl : raw3728step2Labels = raw3728step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3728step1 raw3728step1Labels permutation26 permutation2
    _ = mixedMoment B node2284 node2284Labels := by rfl

def raw3729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3729 raw3729Labels = mixedMoment B node2283 node2283Labels := by
  calc
    mixedMoment B raw3729 raw3729Labels = mixedMoment B raw3729step0 raw3729step0Labels := by
      have hz : ∀ j, raw3729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3729step0 = (fun i j => raw3729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3729step0 raw3729; decide +kernel
      have hl : raw3729step0Labels = raw3729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3729 raw3729Labels permutation346 hz
    mixedMoment B raw3729step0 raw3729step0Labels = mixedMoment B raw3729step1 raw3729step1Labels := by
      have ha : raw3729step1 = (fun i j => raw3729step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3729step1 raw3729step0; decide +kernel
      have hl : raw3729step1Labels = raw3729step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3729step0 raw3729step0Labels permutation128 permutation2
    _ = mixedMoment B node2283 node2283Labels := by rfl

def raw3730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3730 raw3730Labels = mixedMoment B node1066 node1066Labels := by
  calc
    mixedMoment B raw3730 raw3730Labels = mixedMoment B raw3730step0 raw3730step0Labels := by
      have hz : ∀ j, raw3730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3730step0 = (fun i j => raw3730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3730step0 raw3730; decide +kernel
      have hl : raw3730step0Labels = raw3730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3730 raw3730Labels permutation346 hz
    mixedMoment B raw3730step0 raw3730step0Labels = mixedMoment B raw3730step1 raw3730step1Labels := by
      have ha : raw3730step1 = (fun i j => raw3730step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3730step1 raw3730step0; decide +kernel
      have hl : raw3730step1Labels = raw3730step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3730step0 raw3730step0Labels permutation128 permutation2
    _ = mixedMoment B node1066 node1066Labels := by rfl

def raw3731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3731 raw3731Labels = mixedMoment B node2040 node2040Labels := by
  calc
    mixedMoment B raw3731 raw3731Labels = mixedMoment B raw3731step0 raw3731step0Labels := by
      have ha : raw3731step0 = (fun i j => raw3731 (permutation602 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3731step0 raw3731; decide +kernel
      have hl : raw3731step0Labels = raw3731Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3731 raw3731Labels permutation602 permutation2
    _ = mixedMoment B node2040 node2040Labels := by rfl

def raw3732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3732 raw3732Labels = mixedMoment B node2042 node2042Labels := by
  calc
    mixedMoment B raw3732 raw3732Labels = mixedMoment B raw3732step0 raw3732step0Labels := by
      have hz : ∀ j, raw3732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3732step0 = (fun i j => raw3732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3732step0 raw3732; decide +kernel
      have hl : raw3732step0Labels = raw3732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3732 raw3732Labels permutation346 hz
    mixedMoment B raw3732step0 raw3732step0Labels = mixedMoment B raw3732step1 raw3732step1Labels := by
      have ha : raw3732step1 = (fun i j => raw3732step0 (permutation134 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3732step1 raw3732step0; decide +kernel
      have hl : raw3732step1Labels = raw3732step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3732step0 raw3732step0Labels permutation134 permutation2
    _ = mixedMoment B node2042 node2042Labels := by rfl

def raw3733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3733 raw3733Labels = mixedMoment B node2041 node2041Labels := by
  calc
    mixedMoment B raw3733 raw3733Labels = mixedMoment B raw3733step0 raw3733step0Labels := by
      have hz : ∀ j, raw3733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3733step0 = (fun i j => raw3733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3733step0 raw3733; decide +kernel
      have hl : raw3733step0Labels = raw3733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3733 raw3733Labels permutation346 hz
    mixedMoment B raw3733step0 raw3733step0Labels = mixedMoment B raw3733step1 raw3733step1Labels := by
      have ha : raw3733step1 = (fun i j => raw3733step0 (permutation134 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3733step1 raw3733step0; decide +kernel
      have hl : raw3733step1Labels = raw3733step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3733step0 raw3733step0Labels permutation134 permutation2
    _ = mixedMoment B node2041 node2041Labels := by rfl

def raw3734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw3734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3734 raw3734Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw3734 raw3734Labels = mixedMoment B raw3734step0 raw3734step0Labels := by
      have hz : ∀ j, raw3734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3734step0 = (fun i j => raw3734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3734step0 raw3734; decide +kernel
      have hl : raw3734step0Labels = raw3734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3734 raw3734Labels permutation346 hz
    mixedMoment B raw3734step0 raw3734step0Labels = mixedMoment B raw3734step1 raw3734step1Labels := by
      have ha : raw3734step1 = (fun i j => raw3734step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3734step1 raw3734step0; decide +kernel
      have hl : raw3734step1Labels = raw3734step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3734step0 raw3734step0Labels permutation33 permutation4
    mixedMoment B raw3734step1 raw3734step1Labels = mixedMoment B raw3734step2 raw3734step2Labels := by
      have ha : raw3734step2 = -raw3734step1 := by apply Matrix.ext; change ∀ i j, raw3734step2 i j = -(raw3734step1 i j); unfold raw3734step2 raw3734step1; decide +kernel
      have hl : raw3734step2Labels = raw3734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2055 node2055Labels := by rfl

def raw3735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3735 raw3735Labels = mixedMoment B node2042 node2042Labels := by
  calc
    mixedMoment B raw3735 raw3735Labels = mixedMoment B raw3735step0 raw3735step0Labels := by
      have hz : ∀ j, raw3735 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3735step0 = (fun i j => raw3735 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3735step0 raw3735; decide +kernel
      have hl : raw3735step0Labels = raw3735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3735 raw3735Labels permutation265 hz
    mixedMoment B raw3735step0 raw3735step0Labels = mixedMoment B raw3735step1 raw3735step1Labels := by
      have ha : raw3735step1 = (fun i j => raw3735step0 (permutation134 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3735step1 raw3735step0; decide +kernel
      have hl : raw3735step1Labels = raw3735step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3735step0 raw3735step0Labels permutation134 permutation2
    _ = mixedMoment B node2042 node2042Labels := by rfl

def raw3736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3736 raw3736Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw3736 raw3736Labels = mixedMoment B raw3736step0 raw3736step0Labels := by
      have hz : ∀ j, raw3736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3736step0 = (fun i j => raw3736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3736step0 raw3736; decide +kernel
      have hl : raw3736step0Labels = raw3736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3736 raw3736Labels permutation346 hz
    mixedMoment B raw3736step0 raw3736step0Labels = mixedMoment B raw3736step1 raw3736step1Labels := by
      have hz : ∀ j, raw3736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3736step1 = (fun i j => raw3736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3736step1 raw3736step0; decide +kernel
      have hl : raw3736step1Labels = raw3736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3736step0 raw3736step0Labels permutation56 hz
    mixedMoment B raw3736step1 raw3736step1Labels = mixedMoment B raw3736step2 raw3736step2Labels := by
      have ha : raw3736step2 = (fun i j => raw3736step1 (permutation27 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3736step2 raw3736step1; decide +kernel
      have hl : raw3736step2Labels = raw3736step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3736step1 raw3736step1Labels permutation27 permutation2
    _ = mixedMoment B node2284 node2284Labels := by rfl

def raw3737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3737 raw3737Labels = mixedMoment B node1068 node1068Labels := by
  calc
    mixedMoment B raw3737 raw3737Labels = mixedMoment B raw3737step0 raw3737step0Labels := by
      have hz : ∀ j, raw3737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3737step0 = (fun i j => raw3737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3737step0 raw3737; decide +kernel
      have hl : raw3737step0Labels = raw3737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3737 raw3737Labels permutation346 hz
    mixedMoment B raw3737step0 raw3737step0Labels = mixedMoment B raw3737step1 raw3737step1Labels := by
      have hz : ∀ j, raw3737step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3737step1 = (fun i j => raw3737step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3737step1 raw3737step0; decide +kernel
      have hl : raw3737step1Labels = raw3737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3737step0 raw3737step0Labels permutation56 hz
    mixedMoment B raw3737step1 raw3737step1Labels = mixedMoment B raw3737step2 raw3737step2Labels := by
      have ha : raw3737step2 = (fun i j => raw3737step1 (permutation26 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3737step2 raw3737step1; decide +kernel
      have hl : raw3737step2Labels = raw3737step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3737step1 raw3737step1Labels permutation26 permutation2
    _ = mixedMoment B node1068 node1068Labels := by rfl

def raw3738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3738step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3738 raw3738Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw3738 raw3738Labels = mixedMoment B raw3738step0 raw3738step0Labels := by
      have ha : raw3738step0 = (fun i j => raw3738 (permutation595 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3738step0 raw3738; decide +kernel
      have hl : raw3738step0Labels = raw3738Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3738 raw3738Labels permutation595 permutation5
    mixedMoment B raw3738step0 raw3738step0Labels = mixedMoment B raw3738step1 raw3738step1Labels := by
      have ha : raw3738step1 = raw3738step0 := by apply Matrix.ext; unfold raw3738step1 raw3738step0; decide +kernel
      have hl : raw3738step0Labels = labelEmbedding8 ∘ raw3738step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3738step0 raw3738step0Labels raw3738step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

def raw3739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3739step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3739step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3739 raw3739Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw3739 raw3739Labels = mixedMoment B raw3739step0 raw3739step0Labels := by
      have hz : ∀ j, raw3739 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3739step0 = (fun i j => raw3739 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3739step0 raw3739; decide +kernel
      have hl : raw3739step0Labels = raw3739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3739 raw3739Labels permutation265 hz
    mixedMoment B raw3739step0 raw3739step0Labels = mixedMoment B raw3739step1 raw3739step1Labels := by
      have ha : raw3739step1 = (fun i j => raw3739step0 (permutation131 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3739step1 raw3739step0; decide +kernel
      have hl : raw3739step1Labels = raw3739step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3739step0 raw3739step0Labels permutation131 permutation5
    mixedMoment B raw3739step1 raw3739step1Labels = mixedMoment B raw3739step2 raw3739step2Labels := by
      have ha : raw3739step2 = raw3739step1 := by apply Matrix.ext; unfold raw3739step2 raw3739step1; decide +kernel
      have hl : raw3739step1Labels = labelEmbedding8 ∘ raw3739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3739step1 raw3739step1Labels raw3739step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw3740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3740step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3740step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3740 raw3740Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw3740 raw3740Labels = mixedMoment B raw3740step0 raw3740step0Labels := by
      have hz : ∀ j, raw3740 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3740step0 = (fun i j => raw3740 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3740step0 raw3740; decide +kernel
      have hl : raw3740step0Labels = raw3740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3740 raw3740Labels permutation265 hz
    mixedMoment B raw3740step0 raw3740step0Labels = mixedMoment B raw3740step1 raw3740step1Labels := by
      have ha : raw3740step1 = (fun i j => raw3740step0 (permutation129 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3740step1 raw3740step0; decide +kernel
      have hl : raw3740step1Labels = raw3740step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3740step0 raw3740step0Labels permutation129 permutation5
    mixedMoment B raw3740step1 raw3740step1Labels = mixedMoment B raw3740step2 raw3740step2Labels := by
      have ha : raw3740step2 = raw3740step1 := by apply Matrix.ext; unfold raw3740step2 raw3740step1; decide +kernel
      have hl : raw3740step1Labels = labelEmbedding8 ∘ raw3740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3740step1 raw3740step1Labels raw3740step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw3741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3741step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3741step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3741 raw3741Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw3741 raw3741Labels = mixedMoment B raw3741step0 raw3741step0Labels := by
      have hz : ∀ j, raw3741 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3741step0 = (fun i j => raw3741 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3741step0 raw3741; decide +kernel
      have hl : raw3741step0Labels = raw3741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3741 raw3741Labels permutation265 hz
    mixedMoment B raw3741step0 raw3741step0Labels = mixedMoment B raw3741step1 raw3741step1Labels := by
      have ha : raw3741step1 = (fun i j => raw3741step0 (permutation128 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3741step1 raw3741step0; decide +kernel
      have hl : raw3741step1Labels = raw3741step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3741step0 raw3741step0Labels permutation128 permutation5
    mixedMoment B raw3741step1 raw3741step1Labels = mixedMoment B raw3741step2 raw3741step2Labels := by
      have ha : raw3741step2 = raw3741step1 := by apply Matrix.ext; unfold raw3741step2 raw3741step1; decide +kernel
      have hl : raw3741step1Labels = labelEmbedding8 ∘ raw3741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3741step1 raw3741step1Labels raw3741step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw3742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw3742step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3742step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3742step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3742 raw3742Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw3742 raw3742Labels = mixedMoment B raw3742step0 raw3742step0Labels := by
      have hz : ∀ j, raw3742 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3742step0 = (fun i j => raw3742 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3742step0 raw3742; decide +kernel
      have hl : raw3742step0Labels = raw3742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3742 raw3742Labels permutation265 hz
    mixedMoment B raw3742step0 raw3742step0Labels = mixedMoment B raw3742step1 raw3742step1Labels := by
      have ha : raw3742step1 = (fun i j => raw3742step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3742step1 raw3742step0; decide +kernel
      have hl : raw3742step1Labels = raw3742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3742step0 raw3742step0Labels permutation50 permutation7
    mixedMoment B raw3742step1 raw3742step1Labels = mixedMoment B raw3742step2 raw3742step2Labels := by
      have ha : raw3742step2 = -raw3742step1 := by apply Matrix.ext; change ∀ i j, raw3742step2 i j = -(raw3742step1 i j); unfold raw3742step2 raw3742step1; decide +kernel
      have hl : raw3742step2Labels = raw3742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3742step2 raw3742step2Labels = mixedMoment B raw3742step3 raw3742step3Labels := by
      have ha : raw3742step3 = raw3742step2 := by apply Matrix.ext; unfold raw3742step3 raw3742step2; decide +kernel
      have hl : raw3742step2Labels = labelEmbedding10 ∘ raw3742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3742step2 raw3742step2Labels raw3742step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw3743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3743 raw3743Labels = mixedMoment B node4433 node4433Labels := by
  calc
    mixedMoment B raw3743 raw3743Labels = mixedMoment B raw3743step0 raw3743step0Labels := by
      have ha : raw3743step0 = (fun i j => raw3743 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3743step0 raw3743; decide +kernel
      have hl : raw3743step0Labels = raw3743Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3743 raw3743Labels permutation184 permutation2
    _ = mixedMoment B node4433 node4433Labels := by rfl

def raw3744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3744step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3744step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3744step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3744 raw3744Labels = mixedMoment B node4730 node4730Labels := by
  calc
    mixedMoment B raw3744 raw3744Labels = mixedMoment B raw3744step0 raw3744step0Labels := by
      have ha : raw3744step0 = (fun i j => raw3744 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3744step0 raw3744; decide +kernel
      have hl : raw3744step0Labels = raw3744Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3744 raw3744Labels permutation616 permutation3
    mixedMoment B raw3744step0 raw3744step0Labels = mixedMoment B raw3744step1 raw3744step1Labels := by
      have ha : raw3744step1 = -raw3744step0 := by apply Matrix.ext; change ∀ i j, raw3744step1 i j = -(raw3744step0 i j); unfold raw3744step1 raw3744step0; decide +kernel
      have hl : raw3744step1Labels = raw3744step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3744step1 raw3744step1Labels = mixedMoment B raw3744step2 raw3744step2Labels := by
      have ha : raw3744step2 = raw3744step1 := by apply Matrix.ext; unfold raw3744step2 raw3744step1; decide +kernel
      have hl : raw3744step1Labels = labelEmbedding6 ∘ raw3744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3744step1 raw3744step1Labels raw3744step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4730 node4730Labels := by rfl

def raw3745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3745step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3745step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3745step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3745step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3745 raw3745Labels = mixedMoment B node4730 node4730Labels := by
  calc
    mixedMoment B raw3745 raw3745Labels = mixedMoment B raw3745step0 raw3745step0Labels := by
      have ha : raw3745step0 = (fun i j => raw3745 (permutation611 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3745step0 raw3745; decide +kernel
      have hl : raw3745step0Labels = raw3745Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3745 raw3745Labels permutation611 permutation3
    mixedMoment B raw3745step0 raw3745step0Labels = mixedMoment B raw3745step1 raw3745step1Labels := by
      have ha : raw3745step1 = -raw3745step0 := by apply Matrix.ext; change ∀ i j, raw3745step1 i j = -(raw3745step0 i j); unfold raw3745step1 raw3745step0; decide +kernel
      have hl : raw3745step1Labels = raw3745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3745step1 raw3745step1Labels = mixedMoment B raw3745step2 raw3745step2Labels := by
      have ha : raw3745step2 = raw3745step1 := by apply Matrix.ext; unfold raw3745step2 raw3745step1; decide +kernel
      have hl : raw3745step1Labels = labelEmbedding6 ∘ raw3745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3745step1 raw3745step1Labels raw3745step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4730 node4730Labels := by rfl

def raw3746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3746step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3746step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3746step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3746step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3746 raw3746Labels = mixedMoment B node4730 node4730Labels := by
  calc
    mixedMoment B raw3746 raw3746Labels = mixedMoment B raw3746step0 raw3746step0Labels := by
      have ha : raw3746step0 = (fun i j => raw3746 (permutation609 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3746step0 raw3746; decide +kernel
      have hl : raw3746step0Labels = raw3746Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3746 raw3746Labels permutation609 permutation3
    mixedMoment B raw3746step0 raw3746step0Labels = mixedMoment B raw3746step1 raw3746step1Labels := by
      have ha : raw3746step1 = -raw3746step0 := by apply Matrix.ext; change ∀ i j, raw3746step1 i j = -(raw3746step0 i j); unfold raw3746step1 raw3746step0; decide +kernel
      have hl : raw3746step1Labels = raw3746step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3746step1 raw3746step1Labels = mixedMoment B raw3746step2 raw3746step2Labels := by
      have ha : raw3746step2 = raw3746step1 := by apply Matrix.ext; unfold raw3746step2 raw3746step1; decide +kernel
      have hl : raw3746step1Labels = labelEmbedding6 ∘ raw3746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3746step1 raw3746step1Labels raw3746step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4730 node4730Labels := by rfl

def raw3747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw3747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3747 raw3747Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw3747 raw3747Labels = mixedMoment B raw3747step0 raw3747step0Labels := by
      have ha : raw3747step0 = (fun i j => raw3747 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3747step0 raw3747; decide +kernel
      have hl : raw3747step0Labels = raw3747Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3747 raw3747Labels permutation184 permutation2
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw3748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3748 raw3748Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw3748 raw3748Labels = mixedMoment B raw3748step0 raw3748step0Labels := by
      have hz : ∀ j, raw3748 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3748step0 = (fun i j => raw3748 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3748step0 raw3748; decide +kernel
      have hl : raw3748step0Labels = raw3748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3748 raw3748Labels permutation265 hz
    mixedMoment B raw3748step0 raw3748step0Labels = mixedMoment B raw3748step1 raw3748step1Labels := by
      have ha : raw3748step1 = (fun i j => raw3748step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3748step1 raw3748step0; decide +kernel
      have hl : raw3748step1Labels = raw3748step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3748step0 raw3748step0Labels permutation40 permutation2
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw3749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3749 raw3749Labels = mixedMoment B node4793 node4793Labels := by
  calc
    mixedMoment B raw3749 raw3749Labels = mixedMoment B raw3749step0 raw3749step0Labels := by
      have ha : raw3749step0 = (fun i j => raw3749 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3749step0 raw3749; decide +kernel
      have hl : raw3749step0Labels = raw3749Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3749 raw3749Labels permutation160 permutation2
    _ = mixedMoment B node4793 node4793Labels := by rfl

def raw3750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3750step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3750step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3750step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3750step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3750 raw3750Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw3750 raw3750Labels = mixedMoment B raw3750step0 raw3750step0Labels := by
      have hz : ∀ j, raw3750 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3750step0 = (fun i j => raw3750 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3750step0 raw3750; decide +kernel
      have hl : raw3750step0Labels = raw3750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3750 raw3750Labels permutation265 hz
    mixedMoment B raw3750step0 raw3750step0Labels = mixedMoment B raw3750step1 raw3750step1Labels := by
      have ha : raw3750step1 = (fun i j => raw3750step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3750step1 raw3750step0; decide +kernel
      have hl : raw3750step1Labels = raw3750step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3750step0 raw3750step0Labels permutation139 permutation3
    mixedMoment B raw3750step1 raw3750step1Labels = mixedMoment B raw3750step2 raw3750step2Labels := by
      have ha : raw3750step2 = -raw3750step1 := by apply Matrix.ext; change ∀ i j, raw3750step2 i j = -(raw3750step1 i j); unfold raw3750step2 raw3750step1; decide +kernel
      have hl : raw3750step2Labels = raw3750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3750step2 raw3750step2Labels = mixedMoment B raw3750step3 raw3750step3Labels := by
      have ha : raw3750step3 = raw3750step2 := by apply Matrix.ext; unfold raw3750step3 raw3750step2; decide +kernel
      have hl : raw3750step2Labels = labelEmbedding6 ∘ raw3750step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3750step2 raw3750step2Labels raw3750step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw3751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3751step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3751step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3751step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3751step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3751 raw3751Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw3751 raw3751Labels = mixedMoment B raw3751step0 raw3751step0Labels := by
      have hz : ∀ j, raw3751 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3751step0 = (fun i j => raw3751 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3751step0 raw3751; decide +kernel
      have hl : raw3751step0Labels = raw3751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3751 raw3751Labels permutation265 hz
    mixedMoment B raw3751step0 raw3751step0Labels = mixedMoment B raw3751step1 raw3751step1Labels := by
      have ha : raw3751step1 = (fun i j => raw3751step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3751step1 raw3751step0; decide +kernel
      have hl : raw3751step1Labels = raw3751step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3751step0 raw3751step0Labels permutation137 permutation3
    mixedMoment B raw3751step1 raw3751step1Labels = mixedMoment B raw3751step2 raw3751step2Labels := by
      have ha : raw3751step2 = -raw3751step1 := by apply Matrix.ext; change ∀ i j, raw3751step2 i j = -(raw3751step1 i j); unfold raw3751step2 raw3751step1; decide +kernel
      have hl : raw3751step2Labels = raw3751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3751step2 raw3751step2Labels = mixedMoment B raw3751step3 raw3751step3Labels := by
      have ha : raw3751step3 = raw3751step2 := by apply Matrix.ext; unfold raw3751step3 raw3751step2; decide +kernel
      have hl : raw3751step2Labels = labelEmbedding6 ∘ raw3751step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3751step2 raw3751step2Labels raw3751step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw3752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3752 raw3752Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw3752 raw3752Labels = mixedMoment B raw3752step0 raw3752step0Labels := by
      have hz : ∀ j, raw3752 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3752step0 = (fun i j => raw3752 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3752step0 raw3752; decide +kernel
      have hl : raw3752step0Labels = raw3752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3752 raw3752Labels permutation265 hz
    mixedMoment B raw3752step0 raw3752step0Labels = mixedMoment B raw3752step1 raw3752step1Labels := by
      have ha : raw3752step1 = (fun i j => raw3752step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3752step1 raw3752step0; decide +kernel
      have hl : raw3752step1Labels = raw3752step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3752step0 raw3752step0Labels permutation40 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw3753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3753 raw3753Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw3753 raw3753Labels = mixedMoment B raw3753step0 raw3753step0Labels := by
      have hz : ∀ j, raw3753 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3753step0 = (fun i j => raw3753 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3753step0 raw3753; decide +kernel
      have hl : raw3753step0Labels = raw3753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3753 raw3753Labels permutation265 hz
    mixedMoment B raw3753step0 raw3753step0Labels = mixedMoment B raw3753step1 raw3753step1Labels := by
      have ha : raw3753step1 = (fun i j => raw3753step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3753step1 raw3753step0; decide +kernel
      have hl : raw3753step1Labels = raw3753step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3753step0 raw3753step0Labels permutation34 permutation2
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw3754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3754 raw3754Labels = mixedMoment B node4793 node4793Labels := by
  calc
    mixedMoment B raw3754 raw3754Labels = mixedMoment B raw3754step0 raw3754step0Labels := by
      have ha : raw3754step0 = (fun i j => raw3754 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3754step0 raw3754; decide +kernel
      have hl : raw3754step0Labels = raw3754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3754 raw3754Labels permutation154 permutation2
    _ = mixedMoment B node4793 node4793Labels := by rfl

def raw3755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3755step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3755step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3755step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3755step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3755 raw3755Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw3755 raw3755Labels = mixedMoment B raw3755step0 raw3755step0Labels := by
      have hz : ∀ j, raw3755 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3755step0 = (fun i j => raw3755 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3755step0 raw3755; decide +kernel
      have hl : raw3755step0Labels = raw3755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3755 raw3755Labels permutation265 hz
    mixedMoment B raw3755step0 raw3755step0Labels = mixedMoment B raw3755step1 raw3755step1Labels := by
      have ha : raw3755step1 = (fun i j => raw3755step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3755step1 raw3755step0; decide +kernel
      have hl : raw3755step1Labels = raw3755step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3755step0 raw3755step0Labels permutation145 permutation3
    mixedMoment B raw3755step1 raw3755step1Labels = mixedMoment B raw3755step2 raw3755step2Labels := by
      have ha : raw3755step2 = -raw3755step1 := by apply Matrix.ext; change ∀ i j, raw3755step2 i j = -(raw3755step1 i j); unfold raw3755step2 raw3755step1; decide +kernel
      have hl : raw3755step2Labels = raw3755step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3755step2 raw3755step2Labels = mixedMoment B raw3755step3 raw3755step3Labels := by
      have ha : raw3755step3 = raw3755step2 := by apply Matrix.ext; unfold raw3755step3 raw3755step2; decide +kernel
      have hl : raw3755step2Labels = labelEmbedding6 ∘ raw3755step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3755step2 raw3755step2Labels raw3755step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw3756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3756step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3756step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3756 raw3756Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw3756 raw3756Labels = mixedMoment B raw3756step0 raw3756step0Labels := by
      have hz : ∀ j, raw3756 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3756step0 = (fun i j => raw3756 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3756step0 raw3756; decide +kernel
      have hl : raw3756step0Labels = raw3756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3756 raw3756Labels permutation265 hz
    mixedMoment B raw3756step0 raw3756step0Labels = mixedMoment B raw3756step1 raw3756step1Labels := by
      have ha : raw3756step1 = (fun i j => raw3756step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3756step1 raw3756step0; decide +kernel
      have hl : raw3756step1Labels = raw3756step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3756step0 raw3756step0Labels permutation143 permutation3
    mixedMoment B raw3756step1 raw3756step1Labels = mixedMoment B raw3756step2 raw3756step2Labels := by
      have ha : raw3756step2 = -raw3756step1 := by apply Matrix.ext; change ∀ i j, raw3756step2 i j = -(raw3756step1 i j); unfold raw3756step2 raw3756step1; decide +kernel
      have hl : raw3756step2Labels = raw3756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3756step2 raw3756step2Labels = mixedMoment B raw3756step3 raw3756step3Labels := by
      have ha : raw3756step3 = raw3756step2 := by apply Matrix.ext; unfold raw3756step3 raw3756step2; decide +kernel
      have hl : raw3756step2Labels = labelEmbedding6 ∘ raw3756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3756step2 raw3756step2Labels raw3756step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw3757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3757 raw3757Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw3757 raw3757Labels = mixedMoment B raw3757step0 raw3757step0Labels := by
      have hz : ∀ j, raw3757 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3757step0 = (fun i j => raw3757 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3757step0 raw3757; decide +kernel
      have hl : raw3757step0Labels = raw3757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3757 raw3757Labels permutation265 hz
    mixedMoment B raw3757step0 raw3757step0Labels = mixedMoment B raw3757step1 raw3757step1Labels := by
      have ha : raw3757step1 = (fun i j => raw3757step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3757step1 raw3757step0; decide +kernel
      have hl : raw3757step1Labels = raw3757step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3757step0 raw3757step0Labels permutation34 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw3758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3758 raw3758Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw3758 raw3758Labels = mixedMoment B raw3758step0 raw3758step0Labels := by
      have hz : ∀ j, raw3758 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3758step0 = (fun i j => raw3758 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3758step0 raw3758; decide +kernel
      have hl : raw3758step0Labels = raw3758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3758 raw3758Labels permutation265 hz
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw3759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3759 raw3759Labels = mixedMoment B node4793 node4793Labels := by
  calc
    _ = mixedMoment B node4793 node4793Labels := by rfl

def raw3760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3760step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3760step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3760step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3760step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3760 raw3760Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw3760 raw3760Labels = mixedMoment B raw3760step0 raw3760step0Labels := by
      have hz : ∀ j, raw3760 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3760step0 = (fun i j => raw3760 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3760step0 raw3760; decide +kernel
      have hl : raw3760step0Labels = raw3760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3760 raw3760Labels permutation265 hz
    mixedMoment B raw3760step0 raw3760step0Labels = mixedMoment B raw3760step1 raw3760step1Labels := by
      have ha : raw3760step1 = (fun i j => raw3760step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3760step1 raw3760step0; decide +kernel
      have hl : raw3760step1Labels = raw3760step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3760step0 raw3760step0Labels permutation151 permutation3
    mixedMoment B raw3760step1 raw3760step1Labels = mixedMoment B raw3760step2 raw3760step2Labels := by
      have ha : raw3760step2 = -raw3760step1 := by apply Matrix.ext; change ∀ i j, raw3760step2 i j = -(raw3760step1 i j); unfold raw3760step2 raw3760step1; decide +kernel
      have hl : raw3760step2Labels = raw3760step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3760step2 raw3760step2Labels = mixedMoment B raw3760step3 raw3760step3Labels := by
      have ha : raw3760step3 = raw3760step2 := by apply Matrix.ext; unfold raw3760step3 raw3760step2; decide +kernel
      have hl : raw3760step2Labels = labelEmbedding6 ∘ raw3760step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3760step2 raw3760step2Labels raw3760step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw3761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3761step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3761step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3761step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3761step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3761 raw3761Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw3761 raw3761Labels = mixedMoment B raw3761step0 raw3761step0Labels := by
      have hz : ∀ j, raw3761 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3761step0 = (fun i j => raw3761 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3761step0 raw3761; decide +kernel
      have hl : raw3761step0Labels = raw3761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3761 raw3761Labels permutation265 hz
    mixedMoment B raw3761step0 raw3761step0Labels = mixedMoment B raw3761step1 raw3761step1Labels := by
      have ha : raw3761step1 = (fun i j => raw3761step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3761step1 raw3761step0; decide +kernel
      have hl : raw3761step1Labels = raw3761step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3761step0 raw3761step0Labels permutation149 permutation3
    mixedMoment B raw3761step1 raw3761step1Labels = mixedMoment B raw3761step2 raw3761step2Labels := by
      have ha : raw3761step2 = -raw3761step1 := by apply Matrix.ext; change ∀ i j, raw3761step2 i j = -(raw3761step1 i j); unfold raw3761step2 raw3761step1; decide +kernel
      have hl : raw3761step2Labels = raw3761step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3761step2 raw3761step2Labels = mixedMoment B raw3761step3 raw3761step3Labels := by
      have ha : raw3761step3 = raw3761step2 := by apply Matrix.ext; unfold raw3761step3 raw3761step2; decide +kernel
      have hl : raw3761step2Labels = labelEmbedding6 ∘ raw3761step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3761step2 raw3761step2Labels raw3761step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw3762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3762 raw3762Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw3762 raw3762Labels = mixedMoment B raw3762step0 raw3762step0Labels := by
      have hz : ∀ j, raw3762 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3762step0 = (fun i j => raw3762 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3762step0 raw3762; decide +kernel
      have hl : raw3762step0Labels = raw3762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3762 raw3762Labels permutation265 hz
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw3763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw3763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw3763step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3763step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw3763step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3763 raw3763Labels = mixedMoment B node4247 node4247Labels := by
  calc
    mixedMoment B raw3763 raw3763Labels = mixedMoment B raw3763step0 raw3763step0Labels := by
      have hz : ∀ j, raw3763 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3763step0 = (fun i j => raw3763 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3763step0 raw3763; decide +kernel
      have hl : raw3763step0Labels = raw3763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3763 raw3763Labels permutation265 hz
    mixedMoment B raw3763step0 raw3763step0Labels = mixedMoment B raw3763step1 raw3763step1Labels := by
      have ha : raw3763step1 = (fun i j => raw3763step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3763step1 raw3763step0; decide +kernel
      have hl : raw3763step1Labels = raw3763step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3763step0 raw3763step0Labels permutation137 permutation3
    mixedMoment B raw3763step1 raw3763step1Labels = mixedMoment B raw3763step2 raw3763step2Labels := by
      have ha : raw3763step2 = -raw3763step1 := by apply Matrix.ext; change ∀ i j, raw3763step2 i j = -(raw3763step1 i j); unfold raw3763step2 raw3763step1; decide +kernel
      have hl : raw3763step2Labels = raw3763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3763step2 raw3763step2Labels = mixedMoment B raw3763step3 raw3763step3Labels := by
      have ha : raw3763step3 = raw3763step2 := by apply Matrix.ext; unfold raw3763step3 raw3763step2; decide +kernel
      have hl : raw3763step2Labels = labelEmbedding6 ∘ raw3763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3763step2 raw3763step2Labels raw3763step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4247 node4247Labels := by rfl

def raw3764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw3764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3764step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3764 raw3764Labels = mixedMoment B node4245 node4245Labels := by
  calc
    mixedMoment B raw3764 raw3764Labels = mixedMoment B raw3764step0 raw3764step0Labels := by
      have ha : raw3764step0 = (fun i j => raw3764 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3764step0 raw3764; decide +kernel
      have hl : raw3764step0Labels = raw3764Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3764 raw3764Labels permutation640 permutation3
    mixedMoment B raw3764step0 raw3764step0Labels = mixedMoment B raw3764step1 raw3764step1Labels := by
      have ha : raw3764step1 = -raw3764step0 := by apply Matrix.ext; change ∀ i j, raw3764step1 i j = -(raw3764step0 i j); unfold raw3764step1 raw3764step0; decide +kernel
      have hl : raw3764step1Labels = raw3764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3764step1 raw3764step1Labels = mixedMoment B raw3764step2 raw3764step2Labels := by
      have ha : raw3764step2 = raw3764step1 := by apply Matrix.ext; unfold raw3764step2 raw3764step1; decide +kernel
      have hl : raw3764step1Labels = labelEmbedding6 ∘ raw3764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3764step1 raw3764step1Labels raw3764step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4245 node4245Labels := by rfl

def raw3765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3765step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3765step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3765step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3765step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3765 raw3765Labels = mixedMoment B node4254 node4254Labels := by
  calc
    mixedMoment B raw3765 raw3765Labels = mixedMoment B raw3765step0 raw3765step0Labels := by
      have hz : ∀ j, raw3765 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3765step0 = (fun i j => raw3765 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3765step0 raw3765; decide +kernel
      have hl : raw3765step0Labels = raw3765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3765 raw3765Labels permutation265 hz
    mixedMoment B raw3765step0 raw3765step0Labels = mixedMoment B raw3765step1 raw3765step1Labels := by
      have ha : raw3765step1 = (fun i j => raw3765step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3765step1 raw3765step0; decide +kernel
      have hl : raw3765step1Labels = raw3765step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3765step0 raw3765step0Labels permutation145 permutation3
    mixedMoment B raw3765step1 raw3765step1Labels = mixedMoment B raw3765step2 raw3765step2Labels := by
      have ha : raw3765step2 = -raw3765step1 := by apply Matrix.ext; change ∀ i j, raw3765step2 i j = -(raw3765step1 i j); unfold raw3765step2 raw3765step1; decide +kernel
      have hl : raw3765step2Labels = raw3765step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3765step2 raw3765step2Labels = mixedMoment B raw3765step3 raw3765step3Labels := by
      have ha : raw3765step3 = raw3765step2 := by apply Matrix.ext; unfold raw3765step3 raw3765step2; decide +kernel
      have hl : raw3765step2Labels = labelEmbedding6 ∘ raw3765step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3765step2 raw3765step2Labels raw3765step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4254 node4254Labels := by rfl

def raw3766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3766step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3766step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3766 raw3766Labels = mixedMoment B node4254 node4254Labels := by
  calc
    mixedMoment B raw3766 raw3766Labels = mixedMoment B raw3766step0 raw3766step0Labels := by
      have hz : ∀ j, raw3766 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3766step0 = (fun i j => raw3766 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3766step0 raw3766; decide +kernel
      have hl : raw3766step0Labels = raw3766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3766 raw3766Labels permutation265 hz
    mixedMoment B raw3766step0 raw3766step0Labels = mixedMoment B raw3766step1 raw3766step1Labels := by
      have ha : raw3766step1 = (fun i j => raw3766step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3766step1 raw3766step0; decide +kernel
      have hl : raw3766step1Labels = raw3766step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3766step0 raw3766step0Labels permutation139 permutation3
    mixedMoment B raw3766step1 raw3766step1Labels = mixedMoment B raw3766step2 raw3766step2Labels := by
      have ha : raw3766step2 = -raw3766step1 := by apply Matrix.ext; change ∀ i j, raw3766step2 i j = -(raw3766step1 i j); unfold raw3766step2 raw3766step1; decide +kernel
      have hl : raw3766step2Labels = raw3766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3766step2 raw3766step2Labels = mixedMoment B raw3766step3 raw3766step3Labels := by
      have ha : raw3766step3 = raw3766step2 := by apply Matrix.ext; unfold raw3766step3 raw3766step2; decide +kernel
      have hl : raw3766step2Labels = labelEmbedding6 ∘ raw3766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3766step2 raw3766step2Labels raw3766step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4254 node4254Labels := by rfl

def raw3767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw3767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw3767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3767step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3767 raw3767Labels = mixedMoment B node4254 node4254Labels := by
  calc
    mixedMoment B raw3767 raw3767Labels = mixedMoment B raw3767step0 raw3767step0Labels := by
      have hz : ∀ j, raw3767 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3767step0 = (fun i j => raw3767 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3767step0 raw3767; decide +kernel
      have hl : raw3767step0Labels = raw3767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3767 raw3767Labels permutation265 hz
    mixedMoment B raw3767step0 raw3767step0Labels = mixedMoment B raw3767step1 raw3767step1Labels := by
      have ha : raw3767step1 = (fun i j => raw3767step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3767step1 raw3767step0; decide +kernel
      have hl : raw3767step1Labels = raw3767step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3767step0 raw3767step0Labels permutation137 permutation3
    mixedMoment B raw3767step1 raw3767step1Labels = mixedMoment B raw3767step2 raw3767step2Labels := by
      have ha : raw3767step2 = -raw3767step1 := by apply Matrix.ext; change ∀ i j, raw3767step2 i j = -(raw3767step1 i j); unfold raw3767step2 raw3767step1; decide +kernel
      have hl : raw3767step2Labels = raw3767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3767step2 raw3767step2Labels = mixedMoment B raw3767step3 raw3767step3Labels := by
      have ha : raw3767step3 = raw3767step2 := by apply Matrix.ext; unfold raw3767step3 raw3767step2; decide +kernel
      have hl : raw3767step2Labels = labelEmbedding6 ∘ raw3767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3767step2 raw3767step2Labels raw3767step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4254 node4254Labels := by rfl

def raw3768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw3768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw3768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3768 raw3768Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw3768 raw3768Labels = mixedMoment B raw3768step0 raw3768step0Labels := by
      have ha : raw3768step0 = (fun i j => raw3768 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3768step0 raw3768; decide +kernel
      have hl : raw3768step0Labels = raw3768Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3768 raw3768Labels permutation640 permutation3
    mixedMoment B raw3768step0 raw3768step0Labels = mixedMoment B raw3768step1 raw3768step1Labels := by
      have ha : raw3768step1 = -raw3768step0 := by apply Matrix.ext; change ∀ i j, raw3768step1 i j = -(raw3768step0 i j); unfold raw3768step1 raw3768step0; decide +kernel
      have hl : raw3768step1Labels = raw3768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2234 node2234Labels := by rfl

def raw3769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw3769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw3769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3769 raw3769Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw3769 raw3769Labels = mixedMoment B raw3769step0 raw3769step0Labels := by
      have hz : ∀ j, raw3769 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3769step0 = (fun i j => raw3769 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3769step0 raw3769; decide +kernel
      have hl : raw3769step0Labels = raw3769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3769 raw3769Labels permutation265 hz
    mixedMoment B raw3769step0 raw3769step0Labels = mixedMoment B raw3769step1 raw3769step1Labels := by
      have ha : raw3769step1 = (fun i j => raw3769step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3769step1 raw3769step0; decide +kernel
      have hl : raw3769step1Labels = raw3769step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3769step0 raw3769step0Labels permutation145 permutation3
    mixedMoment B raw3769step1 raw3769step1Labels = mixedMoment B raw3769step2 raw3769step2Labels := by
      have ha : raw3769step2 = -raw3769step1 := by apply Matrix.ext; change ∀ i j, raw3769step2 i j = -(raw3769step1 i j); unfold raw3769step2 raw3769step1; decide +kernel
      have hl : raw3769step2Labels = raw3769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw3770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3770step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw3770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw3770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3770 raw3770Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw3770 raw3770Labels = mixedMoment B raw3770step0 raw3770step0Labels := by
      have hz : ∀ j, raw3770 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3770step0 = (fun i j => raw3770 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3770step0 raw3770; decide +kernel
      have hl : raw3770step0Labels = raw3770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3770 raw3770Labels permutation265 hz
    mixedMoment B raw3770step0 raw3770step0Labels = mixedMoment B raw3770step1 raw3770step1Labels := by
      have ha : raw3770step1 = (fun i j => raw3770step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3770step1 raw3770step0; decide +kernel
      have hl : raw3770step1Labels = raw3770step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3770step0 raw3770step0Labels permutation139 permutation3
    mixedMoment B raw3770step1 raw3770step1Labels = mixedMoment B raw3770step2 raw3770step2Labels := by
      have ha : raw3770step2 = -raw3770step1 := by apply Matrix.ext; change ∀ i j, raw3770step2 i j = -(raw3770step1 i j); unfold raw3770step2 raw3770step1; decide +kernel
      have hl : raw3770step2Labels = raw3770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw3771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3771step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw3771step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw3771step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3771 raw3771Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw3771 raw3771Labels = mixedMoment B raw3771step0 raw3771step0Labels := by
      have hz : ∀ j, raw3771 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3771step0 = (fun i j => raw3771 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3771step0 raw3771; decide +kernel
      have hl : raw3771step0Labels = raw3771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3771 raw3771Labels permutation265 hz
    mixedMoment B raw3771step0 raw3771step0Labels = mixedMoment B raw3771step1 raw3771step1Labels := by
      have ha : raw3771step1 = (fun i j => raw3771step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3771step1 raw3771step0; decide +kernel
      have hl : raw3771step1Labels = raw3771step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3771step0 raw3771step0Labels permutation137 permutation3
    mixedMoment B raw3771step1 raw3771step1Labels = mixedMoment B raw3771step2 raw3771step2Labels := by
      have ha : raw3771step2 = -raw3771step1 := by apply Matrix.ext; change ∀ i j, raw3771step2 i j = -(raw3771step1 i j); unfold raw3771step2 raw3771step1; decide +kernel
      have hl : raw3771step2Labels = raw3771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw3772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3772step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw3772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3772 raw3772Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw3772 raw3772Labels = mixedMoment B raw3772step0 raw3772step0Labels := by
      have hz : ∀ j, raw3772 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3772step0 = (fun i j => raw3772 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3772step0 raw3772; decide +kernel
      have hl : raw3772step0Labels = raw3772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3772 raw3772Labels permutation265 hz
    mixedMoment B raw3772step0 raw3772step0Labels = mixedMoment B raw3772step1 raw3772step1Labels := by
      have ha : raw3772step1 = (fun i j => raw3772step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3772step1 raw3772step0; decide +kernel
      have hl : raw3772step1Labels = raw3772step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3772step0 raw3772step0Labels permutation50 permutation6
    mixedMoment B raw3772step1 raw3772step1Labels = mixedMoment B raw3772step2 raw3772step2Labels := by
      have ha : raw3772step2 = -raw3772step1 := by apply Matrix.ext; change ∀ i j, raw3772step2 i j = -(raw3772step1 i j); unfold raw3772step2 raw3772step1; decide +kernel
      have hl : raw3772step2Labels = raw3772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw3773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw3773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3773 raw3773Labels = mixedMoment B node1376 node1376Labels := by
  calc
    mixedMoment B raw3773 raw3773Labels = mixedMoment B raw3773step0 raw3773step0Labels := by
      have ha : raw3773step0 = (fun i j => raw3773 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3773step0 raw3773; decide +kernel
      have hl : raw3773step0Labels = raw3773Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3773 raw3773Labels permutation184 permutation3
    _ = mixedMoment B node1376 node1376Labels := by rfl

def raw3774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3774 raw3774Labels = mixedMoment B node1899 node1899Labels := by
  calc
    mixedMoment B raw3774 raw3774Labels = mixedMoment B raw3774step0 raw3774step0Labels := by
      have ha : raw3774step0 = (fun i j => raw3774 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3774step0 raw3774; decide +kernel
      have hl : raw3774step0Labels = raw3774Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3774 raw3774Labels permutation616 permutation3
    mixedMoment B raw3774step0 raw3774step0Labels = mixedMoment B raw3774step1 raw3774step1Labels := by
      have ha : raw3774step1 = -raw3774step0 := by apply Matrix.ext; change ∀ i j, raw3774step1 i j = -(raw3774step0 i j); unfold raw3774step1 raw3774step0; decide +kernel
      have hl : raw3774step1Labels = raw3774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1899 node1899Labels := by rfl

def raw3775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3775 raw3775Labels = mixedMoment B node1899 node1899Labels := by
  calc
    mixedMoment B raw3775 raw3775Labels = mixedMoment B raw3775step0 raw3775step0Labels := by
      have ha : raw3775step0 = (fun i j => raw3775 (permutation611 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3775step0 raw3775; decide +kernel
      have hl : raw3775step0Labels = raw3775Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3775 raw3775Labels permutation611 permutation3
    mixedMoment B raw3775step0 raw3775step0Labels = mixedMoment B raw3775step1 raw3775step1Labels := by
      have ha : raw3775step1 = -raw3775step0 := by apply Matrix.ext; change ∀ i j, raw3775step1 i j = -(raw3775step0 i j); unfold raw3775step1 raw3775step0; decide +kernel
      have hl : raw3775step1Labels = raw3775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1899 node1899Labels := by rfl

def raw3776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3776step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3776 raw3776Labels = mixedMoment B node1899 node1899Labels := by
  calc
    mixedMoment B raw3776 raw3776Labels = mixedMoment B raw3776step0 raw3776step0Labels := by
      have ha : raw3776step0 = (fun i j => raw3776 (permutation609 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3776step0 raw3776; decide +kernel
      have hl : raw3776step0Labels = raw3776Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3776 raw3776Labels permutation609 permutation3
    mixedMoment B raw3776step0 raw3776step0Labels = mixedMoment B raw3776step1 raw3776step1Labels := by
      have ha : raw3776step1 = -raw3776step0 := by apply Matrix.ext; change ∀ i j, raw3776step1 i j = -(raw3776step0 i j); unfold raw3776step1 raw3776step0; decide +kernel
      have hl : raw3776step1Labels = raw3776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1899 node1899Labels := by rfl

def raw3777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw3777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3777step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3777 raw3777Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw3777 raw3777Labels = mixedMoment B raw3777step0 raw3777step0Labels := by
      have ha : raw3777step0 = (fun i j => raw3777 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3777step0 raw3777; decide +kernel
      have hl : raw3777step0Labels = raw3777Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3777 raw3777Labels permutation246 permutation6
    mixedMoment B raw3777step0 raw3777step0Labels = mixedMoment B raw3777step1 raw3777step1Labels := by
      have ha : raw3777step1 = -raw3777step0 := by apply Matrix.ext; change ∀ i j, raw3777step1 i j = -(raw3777step0 i j); unfold raw3777step1 raw3777step0; decide +kernel
      have hl : raw3777step1Labels = raw3777step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3221 node3221Labels := by rfl

def raw3778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw3778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3778 raw3778Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw3778 raw3778Labels = mixedMoment B raw3778step0 raw3778step0Labels := by
      have hz : ∀ j, raw3778 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3778step0 = (fun i j => raw3778 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3778step0 raw3778; decide +kernel
      have hl : raw3778step0Labels = raw3778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3778 raw3778Labels permutation265 hz
    mixedMoment B raw3778step0 raw3778step0Labels = mixedMoment B raw3778step1 raw3778step1Labels := by
      have ha : raw3778step1 = (fun i j => raw3778step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3778step1 raw3778step0; decide +kernel
      have hl : raw3778step1Labels = raw3778step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3778step0 raw3778step0Labels permutation40 permutation3
    _ = mixedMoment B node1385 node1385Labels := by rfl

def raw3779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw3779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3779 raw3779Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw3779 raw3779Labels = mixedMoment B raw3779step0 raw3779step0Labels := by
      have ha : raw3779step0 = (fun i j => raw3779 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3779step0 raw3779; decide +kernel
      have hl : raw3779step0Labels = raw3779Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3779 raw3779Labels permutation640 permutation3
    mixedMoment B raw3779step0 raw3779step0Labels = mixedMoment B raw3779step1 raw3779step1Labels := by
      have ha : raw3779step1 = -raw3779step0 := by apply Matrix.ext; change ∀ i j, raw3779step1 i j = -(raw3779step0 i j); unfold raw3779step1 raw3779step0; decide +kernel
      have hl : raw3779step1Labels = raw3779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2010 node2010Labels := by rfl

def raw3780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3780step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3780 raw3780Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw3780 raw3780Labels = mixedMoment B raw3780step0 raw3780step0Labels := by
      have hz : ∀ j, raw3780 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3780step0 = (fun i j => raw3780 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3780step0 raw3780; decide +kernel
      have hl : raw3780step0Labels = raw3780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3780 raw3780Labels permutation265 hz
    mixedMoment B raw3780step0 raw3780step0Labels = mixedMoment B raw3780step1 raw3780step1Labels := by
      have ha : raw3780step1 = (fun i j => raw3780step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3780step1 raw3780step0; decide +kernel
      have hl : raw3780step1Labels = raw3780step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3780step0 raw3780step0Labels permutation139 permutation3
    mixedMoment B raw3780step1 raw3780step1Labels = mixedMoment B raw3780step2 raw3780step2Labels := by
      have ha : raw3780step2 = -raw3780step1 := by apply Matrix.ext; change ∀ i j, raw3780step2 i j = -(raw3780step1 i j); unfold raw3780step2 raw3780step1; decide +kernel
      have hl : raw3780step2Labels = raw3780step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw3781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3781 raw3781Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw3781 raw3781Labels = mixedMoment B raw3781step0 raw3781step0Labels := by
      have hz : ∀ j, raw3781 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3781step0 = (fun i j => raw3781 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3781step0 raw3781; decide +kernel
      have hl : raw3781step0Labels = raw3781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3781 raw3781Labels permutation265 hz
    mixedMoment B raw3781step0 raw3781step0Labels = mixedMoment B raw3781step1 raw3781step1Labels := by
      have ha : raw3781step1 = (fun i j => raw3781step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3781step1 raw3781step0; decide +kernel
      have hl : raw3781step1Labels = raw3781step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3781step0 raw3781step0Labels permutation137 permutation3
    mixedMoment B raw3781step1 raw3781step1Labels = mixedMoment B raw3781step2 raw3781step2Labels := by
      have ha : raw3781step2 = -raw3781step1 := by apply Matrix.ext; change ∀ i j, raw3781step2 i j = -(raw3781step1 i j); unfold raw3781step2 raw3781step1; decide +kernel
      have hl : raw3781step2Labels = raw3781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw3782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3782 raw3782Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw3782 raw3782Labels = mixedMoment B raw3782step0 raw3782step0Labels := by
      have hz : ∀ j, raw3782 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3782step0 = (fun i j => raw3782 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3782step0 raw3782; decide +kernel
      have hl : raw3782step0Labels = raw3782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3782 raw3782Labels permutation265 hz
    mixedMoment B raw3782step0 raw3782step0Labels = mixedMoment B raw3782step1 raw3782step1Labels := by
      have ha : raw3782step1 = (fun i j => raw3782step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3782step1 raw3782step0; decide +kernel
      have hl : raw3782step1Labels = raw3782step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3782step0 raw3782step0Labels permutation50 permutation6
    mixedMoment B raw3782step1 raw3782step1Labels = mixedMoment B raw3782step2 raw3782step2Labels := by
      have ha : raw3782step2 = -raw3782step1 := by apply Matrix.ext; change ∀ i j, raw3782step2 i j = -(raw3782step1 i j); unfold raw3782step2 raw3782step1; decide +kernel
      have hl : raw3782step2Labels = raw3782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw3783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw3783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3783 raw3783Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw3783 raw3783Labels = mixedMoment B raw3783step0 raw3783step0Labels := by
      have hz : ∀ j, raw3783 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3783step0 = (fun i j => raw3783 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3783step0 raw3783; decide +kernel
      have hl : raw3783step0Labels = raw3783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3783 raw3783Labels permutation265 hz
    mixedMoment B raw3783step0 raw3783step0Labels = mixedMoment B raw3783step1 raw3783step1Labels := by
      have ha : raw3783step1 = (fun i j => raw3783step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3783step1 raw3783step0; decide +kernel
      have hl : raw3783step1Labels = raw3783step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3783step0 raw3783step0Labels permutation34 permutation3
    _ = mixedMoment B node1385 node1385Labels := by rfl

def raw3784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw3784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3784 raw3784Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw3784 raw3784Labels = mixedMoment B raw3784step0 raw3784step0Labels := by
      have ha : raw3784step0 = (fun i j => raw3784 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3784step0 raw3784; decide +kernel
      have hl : raw3784step0Labels = raw3784Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3784 raw3784Labels permutation658 permutation3
    mixedMoment B raw3784step0 raw3784step0Labels = mixedMoment B raw3784step1 raw3784step1Labels := by
      have ha : raw3784step1 = -raw3784step0 := by apply Matrix.ext; change ∀ i j, raw3784step1 i j = -(raw3784step0 i j); unfold raw3784step1 raw3784step0; decide +kernel
      have hl : raw3784step1Labels = raw3784step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2010 node2010Labels := by rfl

def raw3785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3785 raw3785Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw3785 raw3785Labels = mixedMoment B raw3785step0 raw3785step0Labels := by
      have hz : ∀ j, raw3785 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3785step0 = (fun i j => raw3785 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3785step0 raw3785; decide +kernel
      have hl : raw3785step0Labels = raw3785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3785 raw3785Labels permutation265 hz
    mixedMoment B raw3785step0 raw3785step0Labels = mixedMoment B raw3785step1 raw3785step1Labels := by
      have ha : raw3785step1 = (fun i j => raw3785step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3785step1 raw3785step0; decide +kernel
      have hl : raw3785step1Labels = raw3785step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3785step0 raw3785step0Labels permutation145 permutation3
    mixedMoment B raw3785step1 raw3785step1Labels = mixedMoment B raw3785step2 raw3785step2Labels := by
      have ha : raw3785step2 = -raw3785step1 := by apply Matrix.ext; change ∀ i j, raw3785step2 i j = -(raw3785step1 i j); unfold raw3785step2 raw3785step1; decide +kernel
      have hl : raw3785step2Labels = raw3785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw3786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3786 raw3786Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw3786 raw3786Labels = mixedMoment B raw3786step0 raw3786step0Labels := by
      have hz : ∀ j, raw3786 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3786step0 = (fun i j => raw3786 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3786step0 raw3786; decide +kernel
      have hl : raw3786step0Labels = raw3786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3786 raw3786Labels permutation265 hz
    mixedMoment B raw3786step0 raw3786step0Labels = mixedMoment B raw3786step1 raw3786step1Labels := by
      have ha : raw3786step1 = (fun i j => raw3786step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3786step1 raw3786step0; decide +kernel
      have hl : raw3786step1Labels = raw3786step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3786step0 raw3786step0Labels permutation143 permutation3
    mixedMoment B raw3786step1 raw3786step1Labels = mixedMoment B raw3786step2 raw3786step2Labels := by
      have ha : raw3786step2 = -raw3786step1 := by apply Matrix.ext; change ∀ i j, raw3786step2 i j = -(raw3786step1 i j); unfold raw3786step2 raw3786step1; decide +kernel
      have hl : raw3786step2Labels = raw3786step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw3787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3787 raw3787Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw3787 raw3787Labels = mixedMoment B raw3787step0 raw3787step0Labels := by
      have hz : ∀ j, raw3787 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3787step0 = (fun i j => raw3787 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3787step0 raw3787; decide +kernel
      have hl : raw3787step0Labels = raw3787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3787 raw3787Labels permutation265 hz
    mixedMoment B raw3787step0 raw3787step0Labels = mixedMoment B raw3787step1 raw3787step1Labels := by
      have ha : raw3787step1 = (fun i j => raw3787step0 (permutation52 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3787step1 raw3787step0; decide +kernel
      have hl : raw3787step1Labels = raw3787step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3787step0 raw3787step0Labels permutation52 permutation6
    mixedMoment B raw3787step1 raw3787step1Labels = mixedMoment B raw3787step2 raw3787step2Labels := by
      have ha : raw3787step2 = -raw3787step1 := by apply Matrix.ext; change ∀ i j, raw3787step2 i j = -(raw3787step1 i j); unfold raw3787step2 raw3787step1; decide +kernel
      have hl : raw3787step2Labels = raw3787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw3788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw3788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3788 raw3788Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw3788 raw3788Labels = mixedMoment B raw3788step0 raw3788step0Labels := by
      have hz : ∀ j, raw3788 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3788step0 = (fun i j => raw3788 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3788step0 raw3788; decide +kernel
      have hl : raw3788step0Labels = raw3788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3788 raw3788Labels permutation265 hz
    mixedMoment B raw3788step0 raw3788step0Labels = mixedMoment B raw3788step1 raw3788step1Labels := by
      have ha : raw3788step1 = (fun i j => raw3788step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3788step1 raw3788step0; decide +kernel
      have hl : raw3788step1Labels = raw3788step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3788step0 raw3788step0Labels permutation32 permutation3
    _ = mixedMoment B node1385 node1385Labels := by rfl

def raw3789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw3789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3789 raw3789Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw3789 raw3789Labels = mixedMoment B raw3789step0 raw3789step0Labels := by
      have ha : raw3789step0 = (fun i j => raw3789 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3789step0 raw3789; decide +kernel
      have hl : raw3789step0Labels = raw3789Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3789 raw3789Labels permutation682 permutation3
    mixedMoment B raw3789step0 raw3789step0Labels = mixedMoment B raw3789step1 raw3789step1Labels := by
      have ha : raw3789step1 = -raw3789step0 := by apply Matrix.ext; change ∀ i j, raw3789step1 i j = -(raw3789step0 i j); unfold raw3789step1 raw3789step0; decide +kernel
      have hl : raw3789step1Labels = raw3789step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2010 node2010Labels := by rfl

def raw3790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3790 raw3790Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw3790 raw3790Labels = mixedMoment B raw3790step0 raw3790step0Labels := by
      have hz : ∀ j, raw3790 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3790step0 = (fun i j => raw3790 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3790step0 raw3790; decide +kernel
      have hl : raw3790step0Labels = raw3790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3790 raw3790Labels permutation265 hz
    mixedMoment B raw3790step0 raw3790step0Labels = mixedMoment B raw3790step1 raw3790step1Labels := by
      have ha : raw3790step1 = (fun i j => raw3790step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3790step1 raw3790step0; decide +kernel
      have hl : raw3790step1Labels = raw3790step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3790step0 raw3790step0Labels permutation151 permutation3
    mixedMoment B raw3790step1 raw3790step1Labels = mixedMoment B raw3790step2 raw3790step2Labels := by
      have ha : raw3790step2 = -raw3790step1 := by apply Matrix.ext; change ∀ i j, raw3790step2 i j = -(raw3790step1 i j); unfold raw3790step2 raw3790step1; decide +kernel
      have hl : raw3790step2Labels = raw3790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw3791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3791 raw3791Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw3791 raw3791Labels = mixedMoment B raw3791step0 raw3791step0Labels := by
      have hz : ∀ j, raw3791 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3791step0 = (fun i j => raw3791 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3791step0 raw3791; decide +kernel
      have hl : raw3791step0Labels = raw3791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3791 raw3791Labels permutation265 hz
    mixedMoment B raw3791step0 raw3791step0Labels = mixedMoment B raw3791step1 raw3791step1Labels := by
      have ha : raw3791step1 = (fun i j => raw3791step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3791step1 raw3791step0; decide +kernel
      have hl : raw3791step1Labels = raw3791step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3791step0 raw3791step0Labels permutation149 permutation3
    mixedMoment B raw3791step1 raw3791step1Labels = mixedMoment B raw3791step2 raw3791step2Labels := by
      have ha : raw3791step2 = -raw3791step1 := by apply Matrix.ext; change ∀ i j, raw3791step2 i j = -(raw3791step1 i j); unfold raw3791step2 raw3791step1; decide +kernel
      have hl : raw3791step2Labels = raw3791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw3792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3792 raw3792Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw3792 raw3792Labels = mixedMoment B raw3792step0 raw3792step0Labels := by
      have hz : ∀ j, raw3792 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3792step0 = (fun i j => raw3792 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3792step0 raw3792; decide +kernel
      have hl : raw3792step0Labels = raw3792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3792 raw3792Labels permutation265 hz
    mixedMoment B raw3792step0 raw3792step0Labels = mixedMoment B raw3792step1 raw3792step1Labels := by
      have ha : raw3792step1 = (fun i j => raw3792step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3792step1 raw3792step0; decide +kernel
      have hl : raw3792step1Labels = raw3792step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3792step0 raw3792step0Labels permutation54 permutation6
    mixedMoment B raw3792step1 raw3792step1Labels = mixedMoment B raw3792step2 raw3792step2Labels := by
      have ha : raw3792step2 = -raw3792step1 := by apply Matrix.ext; change ∀ i j, raw3792step2 i j = -(raw3792step1 i j); unfold raw3792step2 raw3792step1; decide +kernel
      have hl : raw3792step2Labels = raw3792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw3793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3793step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw3793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw3793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3793 raw3793Labels = mixedMoment B node779 node779Labels := by
  calc
    mixedMoment B raw3793 raw3793Labels = mixedMoment B raw3793step0 raw3793step0Labels := by
      have hz : ∀ j, raw3793 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3793step0 = (fun i j => raw3793 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3793step0 raw3793; decide +kernel
      have hl : raw3793step0Labels = raw3793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3793 raw3793Labels permutation265 hz
    mixedMoment B raw3793step0 raw3793step0Labels = mixedMoment B raw3793step1 raw3793step1Labels := by
      have ha : raw3793step1 = (fun i j => raw3793step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3793step1 raw3793step0; decide +kernel
      have hl : raw3793step1Labels = raw3793step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3793step0 raw3793step0Labels permutation137 permutation3
    mixedMoment B raw3793step1 raw3793step1Labels = mixedMoment B raw3793step2 raw3793step2Labels := by
      have ha : raw3793step2 = -raw3793step1 := by apply Matrix.ext; change ∀ i j, raw3793step2 i j = -(raw3793step1 i j); unfold raw3793step2 raw3793step1; decide +kernel
      have hl : raw3793step2Labels = raw3793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node779 node779Labels := by rfl

def raw3794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw3794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3794 raw3794Labels = mixedMoment B node777 node777Labels := by
  calc
    mixedMoment B raw3794 raw3794Labels = mixedMoment B raw3794step0 raw3794step0Labels := by
      have ha : raw3794step0 = (fun i j => raw3794 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3794step0 raw3794; decide +kernel
      have hl : raw3794step0Labels = raw3794Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3794 raw3794Labels permutation640 permutation3
    mixedMoment B raw3794step0 raw3794step0Labels = mixedMoment B raw3794step1 raw3794step1Labels := by
      have ha : raw3794step1 = -raw3794step0 := by apply Matrix.ext; change ∀ i j, raw3794step1 i j = -(raw3794step0 i j); unfold raw3794step1 raw3794step0; decide +kernel
      have hl : raw3794step1Labels = raw3794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node777 node777Labels := by rfl

def raw3795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3795 raw3795Labels = mixedMoment B node788 node788Labels := by
  calc
    mixedMoment B raw3795 raw3795Labels = mixedMoment B raw3795step0 raw3795step0Labels := by
      have hz : ∀ j, raw3795 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3795step0 = (fun i j => raw3795 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3795step0 raw3795; decide +kernel
      have hl : raw3795step0Labels = raw3795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3795 raw3795Labels permutation265 hz
    mixedMoment B raw3795step0 raw3795step0Labels = mixedMoment B raw3795step1 raw3795step1Labels := by
      have ha : raw3795step1 = (fun i j => raw3795step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3795step1 raw3795step0; decide +kernel
      have hl : raw3795step1Labels = raw3795step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3795step0 raw3795step0Labels permutation145 permutation3
    mixedMoment B raw3795step1 raw3795step1Labels = mixedMoment B raw3795step2 raw3795step2Labels := by
      have ha : raw3795step2 = -raw3795step1 := by apply Matrix.ext; change ∀ i j, raw3795step2 i j = -(raw3795step1 i j); unfold raw3795step2 raw3795step1; decide +kernel
      have hl : raw3795step2Labels = raw3795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node788 node788Labels := by rfl

def raw3796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3796 raw3796Labels = mixedMoment B node788 node788Labels := by
  calc
    mixedMoment B raw3796 raw3796Labels = mixedMoment B raw3796step0 raw3796step0Labels := by
      have hz : ∀ j, raw3796 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3796step0 = (fun i j => raw3796 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3796step0 raw3796; decide +kernel
      have hl : raw3796step0Labels = raw3796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3796 raw3796Labels permutation265 hz
    mixedMoment B raw3796step0 raw3796step0Labels = mixedMoment B raw3796step1 raw3796step1Labels := by
      have ha : raw3796step1 = (fun i j => raw3796step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3796step1 raw3796step0; decide +kernel
      have hl : raw3796step1Labels = raw3796step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3796step0 raw3796step0Labels permutation139 permutation3
    mixedMoment B raw3796step1 raw3796step1Labels = mixedMoment B raw3796step2 raw3796step2Labels := by
      have ha : raw3796step2 = -raw3796step1 := by apply Matrix.ext; change ∀ i j, raw3796step2 i j = -(raw3796step1 i j); unfold raw3796step2 raw3796step1; decide +kernel
      have hl : raw3796step2Labels = raw3796step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node788 node788Labels := by rfl

def raw3797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw3797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw3797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3797 raw3797Labels = mixedMoment B node788 node788Labels := by
  calc
    mixedMoment B raw3797 raw3797Labels = mixedMoment B raw3797step0 raw3797step0Labels := by
      have hz : ∀ j, raw3797 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3797step0 = (fun i j => raw3797 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3797step0 raw3797; decide +kernel
      have hl : raw3797step0Labels = raw3797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3797 raw3797Labels permutation265 hz
    mixedMoment B raw3797step0 raw3797step0Labels = mixedMoment B raw3797step1 raw3797step1Labels := by
      have ha : raw3797step1 = (fun i j => raw3797step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3797step1 raw3797step0; decide +kernel
      have hl : raw3797step1Labels = raw3797step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3797step0 raw3797step0Labels permutation137 permutation3
    mixedMoment B raw3797step1 raw3797step1Labels = mixedMoment B raw3797step2 raw3797step2Labels := by
      have ha : raw3797step2 = -raw3797step1 := by apply Matrix.ext; change ∀ i j, raw3797step2 i j = -(raw3797step1 i j); unfold raw3797step2 raw3797step1; decide +kernel
      have hl : raw3797step2Labels = raw3797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node788 node788Labels := by rfl

def raw3798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3798 raw3798Labels = mixedMoment B node2131 node2131Labels := by
  calc
    mixedMoment B raw3798 raw3798Labels = mixedMoment B raw3798step0 raw3798step0Labels := by
      have ha : raw3798step0 = (fun i j => raw3798 (permutation595 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3798step0 raw3798; decide +kernel
      have hl : raw3798step0Labels = raw3798Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3798 raw3798Labels permutation595 permutation5
    mixedMoment B raw3798step0 raw3798step0Labels = mixedMoment B raw3798step1 raw3798step1Labels := by
      have ha : raw3798step1 = raw3798step0 := by apply Matrix.ext; unfold raw3798step1 raw3798step0; decide +kernel
      have hl : raw3798step0Labels = labelEmbedding1 ∘ raw3798step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3798step0 raw3798step0Labels raw3798step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2131 node2131Labels := by rfl

def raw3799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3799 raw3799Labels = mixedMoment B node2132 node2132Labels := by
  calc
    mixedMoment B raw3799 raw3799Labels = mixedMoment B raw3799step0 raw3799step0Labels := by
      have hz : ∀ j, raw3799 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3799step0 = (fun i j => raw3799 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3799step0 raw3799; decide +kernel
      have hl : raw3799step0Labels = raw3799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3799 raw3799Labels permutation265 hz
    mixedMoment B raw3799step0 raw3799step0Labels = mixedMoment B raw3799step1 raw3799step1Labels := by
      have ha : raw3799step1 = (fun i j => raw3799step0 (permutation131 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3799step1 raw3799step0; decide +kernel
      have hl : raw3799step1Labels = raw3799step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3799step0 raw3799step0Labels permutation131 permutation5
    mixedMoment B raw3799step1 raw3799step1Labels = mixedMoment B raw3799step2 raw3799step2Labels := by
      have ha : raw3799step2 = raw3799step1 := by apply Matrix.ext; unfold raw3799step2 raw3799step1; decide +kernel
      have hl : raw3799step1Labels = labelEmbedding1 ∘ raw3799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3799step1 raw3799step1Labels raw3799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2132 node2132Labels := by rfl

def raw3800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3800 raw3800Labels = mixedMoment B node2132 node2132Labels := by
  calc
    mixedMoment B raw3800 raw3800Labels = mixedMoment B raw3800step0 raw3800step0Labels := by
      have hz : ∀ j, raw3800 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3800step0 = (fun i j => raw3800 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3800step0 raw3800; decide +kernel
      have hl : raw3800step0Labels = raw3800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3800 raw3800Labels permutation265 hz
    mixedMoment B raw3800step0 raw3800step0Labels = mixedMoment B raw3800step1 raw3800step1Labels := by
      have ha : raw3800step1 = (fun i j => raw3800step0 (permutation129 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3800step1 raw3800step0; decide +kernel
      have hl : raw3800step1Labels = raw3800step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3800step0 raw3800step0Labels permutation129 permutation5
    mixedMoment B raw3800step1 raw3800step1Labels = mixedMoment B raw3800step2 raw3800step2Labels := by
      have ha : raw3800step2 = raw3800step1 := by apply Matrix.ext; unfold raw3800step2 raw3800step1; decide +kernel
      have hl : raw3800step1Labels = labelEmbedding1 ∘ raw3800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3800step1 raw3800step1Labels raw3800step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2132 node2132Labels := by rfl

def raw3801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3801 raw3801Labels = mixedMoment B node2132 node2132Labels := by
  calc
    mixedMoment B raw3801 raw3801Labels = mixedMoment B raw3801step0 raw3801step0Labels := by
      have hz : ∀ j, raw3801 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3801step0 = (fun i j => raw3801 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3801step0 raw3801; decide +kernel
      have hl : raw3801step0Labels = raw3801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3801 raw3801Labels permutation265 hz
    mixedMoment B raw3801step0 raw3801step0Labels = mixedMoment B raw3801step1 raw3801step1Labels := by
      have ha : raw3801step1 = (fun i j => raw3801step0 (permutation128 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3801step1 raw3801step0; decide +kernel
      have hl : raw3801step1Labels = raw3801step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3801step0 raw3801step0Labels permutation128 permutation5
    mixedMoment B raw3801step1 raw3801step1Labels = mixedMoment B raw3801step2 raw3801step2Labels := by
      have ha : raw3801step2 = raw3801step1 := by apply Matrix.ext; unfold raw3801step2 raw3801step1; decide +kernel
      have hl : raw3801step1Labels = labelEmbedding1 ∘ raw3801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3801step1 raw3801step1Labels raw3801step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2132 node2132Labels := by rfl

def raw3802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3802step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw3802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3802step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3802step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3802 raw3802Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw3802 raw3802Labels = mixedMoment B raw3802step0 raw3802step0Labels := by
      have hz : ∀ j, raw3802 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3802step0 = (fun i j => raw3802 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3802step0 raw3802; decide +kernel
      have hl : raw3802step0Labels = raw3802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3802 raw3802Labels permutation265 hz
    mixedMoment B raw3802step0 raw3802step0Labels = mixedMoment B raw3802step1 raw3802step1Labels := by
      have ha : raw3802step1 = (fun i j => raw3802step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3802step1 raw3802step0; decide +kernel
      have hl : raw3802step1Labels = raw3802step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3802step0 raw3802step0Labels permutation50 permutation7
    mixedMoment B raw3802step1 raw3802step1Labels = mixedMoment B raw3802step2 raw3802step2Labels := by
      have ha : raw3802step2 = -raw3802step1 := by apply Matrix.ext; change ∀ i j, raw3802step2 i j = -(raw3802step1 i j); unfold raw3802step2 raw3802step1; decide +kernel
      have hl : raw3802step2Labels = raw3802step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3802step2 raw3802step2Labels = mixedMoment B raw3802step3 raw3802step3Labels := by
      have ha : raw3802step3 = raw3802step2 := by apply Matrix.ext; unfold raw3802step3 raw3802step2; decide +kernel
      have hl : raw3802step2Labels = labelEmbedding1 ∘ raw3802step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3802step2 raw3802step2Labels raw3802step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2775 node2775Labels := by rfl

def raw3803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw3803step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3803 raw3803Labels = mixedMoment B node1717 node1717Labels := by
  calc
    mixedMoment B raw3803 raw3803Labels = mixedMoment B raw3803step0 raw3803step0Labels := by
      have ha : raw3803step0 = (fun i j => raw3803 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3803step0 raw3803; decide +kernel
      have hl : raw3803step0Labels = raw3803Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3803 raw3803Labels permutation170 permutation7
    mixedMoment B raw3803step0 raw3803step0Labels = mixedMoment B raw3803step1 raw3803step1Labels := by
      have ha : raw3803step1 = -raw3803step0 := by apply Matrix.ext; change ∀ i j, raw3803step1 i j = -(raw3803step0 i j); unfold raw3803step1 raw3803step0; decide +kernel
      have hl : raw3803step1Labels = raw3803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3803step1 raw3803step1Labels = mixedMoment B raw3803step2 raw3803step2Labels := by
      have ha : raw3803step2 = raw3803step1 := by apply Matrix.ext; unfold raw3803step2 raw3803step1; decide +kernel
      have hl : raw3803step1Labels = labelEmbedding1 ∘ raw3803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3803step1 raw3803step1Labels raw3803step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1717 node1717Labels := by rfl

def raw3804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3804step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3804 raw3804Labels = mixedMoment B node1930 node1930Labels := by
  calc
    mixedMoment B raw3804 raw3804Labels = mixedMoment B raw3804step0 raw3804step0Labels := by
      have ha : raw3804step0 = (fun i j => raw3804 (permutation605 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3804step0 raw3804; decide +kernel
      have hl : raw3804step0Labels = raw3804Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3804 raw3804Labels permutation605 permutation5
    mixedMoment B raw3804step0 raw3804step0Labels = mixedMoment B raw3804step1 raw3804step1Labels := by
      have ha : raw3804step1 = raw3804step0 := by apply Matrix.ext; unfold raw3804step1 raw3804step0; decide +kernel
      have hl : raw3804step0Labels = labelEmbedding1 ∘ raw3804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3804step0 raw3804step0Labels raw3804step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1930 node1930Labels := by rfl

def raw3805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3805step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3805 raw3805Labels = mixedMoment B node1930 node1930Labels := by
  calc
    mixedMoment B raw3805 raw3805Labels = mixedMoment B raw3805step0 raw3805step0Labels := by
      have ha : raw3805step0 = (fun i j => raw3805 (permutation603 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3805step0 raw3805; decide +kernel
      have hl : raw3805step0Labels = raw3805Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3805 raw3805Labels permutation603 permutation5
    mixedMoment B raw3805step0 raw3805step0Labels = mixedMoment B raw3805step1 raw3805step1Labels := by
      have ha : raw3805step1 = raw3805step0 := by apply Matrix.ext; unfold raw3805step1 raw3805step0; decide +kernel
      have hl : raw3805step0Labels = labelEmbedding1 ∘ raw3805step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3805step0 raw3805step0Labels raw3805step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1930 node1930Labels := by rfl

def raw3806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3806 raw3806Labels = mixedMoment B node1930 node1930Labels := by
  calc
    mixedMoment B raw3806 raw3806Labels = mixedMoment B raw3806step0 raw3806step0Labels := by
      have ha : raw3806step0 = (fun i j => raw3806 (permutation602 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3806step0 raw3806; decide +kernel
      have hl : raw3806step0Labels = raw3806Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3806 raw3806Labels permutation602 permutation5
    mixedMoment B raw3806step0 raw3806step0Labels = mixedMoment B raw3806step1 raw3806step1Labels := by
      have ha : raw3806step1 = raw3806step0 := by apply Matrix.ext; unfold raw3806step1 raw3806step0; decide +kernel
      have hl : raw3806step0Labels = labelEmbedding1 ∘ raw3806step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3806step0 raw3806step0Labels raw3806step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1930 node1930Labels := by rfl

def raw3807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw3807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3807 raw3807Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw3807 raw3807Labels = mixedMoment B raw3807step0 raw3807step0Labels := by
      have ha : raw3807step0 = (fun i j => raw3807 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3807step0 raw3807; decide +kernel
      have hl : raw3807step0Labels = raw3807Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3807 raw3807Labels permutation170 permutation7
    mixedMoment B raw3807step0 raw3807step0Labels = mixedMoment B raw3807step1 raw3807step1Labels := by
      have ha : raw3807step1 = -raw3807step0 := by apply Matrix.ext; change ∀ i j, raw3807step1 i j = -(raw3807step0 i j); unfold raw3807step1 raw3807step0; decide +kernel
      have hl : raw3807step1Labels = raw3807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3807step1 raw3807step1Labels = mixedMoment B raw3807step2 raw3807step2Labels := by
      have ha : raw3807step2 = raw3807step1 := by apply Matrix.ext; unfold raw3807step2 raw3807step1; decide +kernel
      have hl : raw3807step1Labels = labelEmbedding1 ∘ raw3807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3807step1 raw3807step1Labels raw3807step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2252 node2252Labels := by rfl

def raw3808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3808 raw3808Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw3808 raw3808Labels = mixedMoment B raw3808step0 raw3808step0Labels := by
      have hz : ∀ j, raw3808 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3808step0 = (fun i j => raw3808 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3808step0 raw3808; decide +kernel
      have hl : raw3808step0Labels = raw3808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3808 raw3808Labels permutation265 hz
    mixedMoment B raw3808step0 raw3808step0Labels = mixedMoment B raw3808step1 raw3808step1Labels := by
      have ha : raw3808step1 = (fun i j => raw3808step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3808step1 raw3808step0; decide +kernel
      have hl : raw3808step1Labels = raw3808step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3808step0 raw3808step0Labels permutation53 permutation7
    mixedMoment B raw3808step1 raw3808step1Labels = mixedMoment B raw3808step2 raw3808step2Labels := by
      have ha : raw3808step2 = -raw3808step1 := by apply Matrix.ext; change ∀ i j, raw3808step2 i j = -(raw3808step1 i j); unfold raw3808step2 raw3808step1; decide +kernel
      have hl : raw3808step2Labels = raw3808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3808step2 raw3808step2Labels = mixedMoment B raw3808step3 raw3808step3Labels := by
      have ha : raw3808step3 = raw3808step2 := by apply Matrix.ext; unfold raw3808step3 raw3808step2; decide +kernel
      have hl : raw3808step2Labels = labelEmbedding1 ∘ raw3808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3808step2 raw3808step2Labels raw3808step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw3809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3809step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3809 raw3809Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw3809 raw3809Labels = mixedMoment B raw3809step0 raw3809step0Labels := by
      have ha : raw3809step0 = (fun i j => raw3809 (permutation626 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3809step0 raw3809; decide +kernel
      have hl : raw3809step0Labels = raw3809Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3809 raw3809Labels permutation626 permutation5
    mixedMoment B raw3809step0 raw3809step0Labels = mixedMoment B raw3809step1 raw3809step1Labels := by
      have ha : raw3809step1 = raw3809step0 := by apply Matrix.ext; unfold raw3809step1 raw3809step0; decide +kernel
      have hl : raw3809step0Labels = labelEmbedding1 ∘ raw3809step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3809step0 raw3809step0Labels raw3809step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2219 node2219Labels := by rfl

def raw3810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3810step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3810 raw3810Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw3810 raw3810Labels = mixedMoment B raw3810step0 raw3810step0Labels := by
      have hz : ∀ j, raw3810 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3810step0 = (fun i j => raw3810 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3810step0 raw3810; decide +kernel
      have hl : raw3810step0Labels = raw3810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3810 raw3810Labels permutation265 hz
    mixedMoment B raw3810step0 raw3810step0Labels = mixedMoment B raw3810step1 raw3810step1Labels := by
      have ha : raw3810step1 = (fun i j => raw3810step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3810step1 raw3810step0; decide +kernel
      have hl : raw3810step1Labels = raw3810step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3810step0 raw3810step0Labels permutation135 permutation5
    mixedMoment B raw3810step1 raw3810step1Labels = mixedMoment B raw3810step2 raw3810step2Labels := by
      have ha : raw3810step2 = raw3810step1 := by apply Matrix.ext; unfold raw3810step2 raw3810step1; decide +kernel
      have hl : raw3810step1Labels = labelEmbedding1 ∘ raw3810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3810step1 raw3810step1Labels raw3810step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw3811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3811step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3811 raw3811Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw3811 raw3811Labels = mixedMoment B raw3811step0 raw3811step0Labels := by
      have hz : ∀ j, raw3811 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3811step0 = (fun i j => raw3811 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3811step0 raw3811; decide +kernel
      have hl : raw3811step0Labels = raw3811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3811 raw3811Labels permutation265 hz
    mixedMoment B raw3811step0 raw3811step0Labels = mixedMoment B raw3811step1 raw3811step1Labels := by
      have ha : raw3811step1 = (fun i j => raw3811step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3811step1 raw3811step0; decide +kernel
      have hl : raw3811step1Labels = raw3811step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3811step0 raw3811step0Labels permutation134 permutation5
    mixedMoment B raw3811step1 raw3811step1Labels = mixedMoment B raw3811step2 raw3811step2Labels := by
      have ha : raw3811step2 = raw3811step1 := by apply Matrix.ext; unfold raw3811step2 raw3811step1; decide +kernel
      have hl : raw3811step1Labels = labelEmbedding1 ∘ raw3811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3811step1 raw3811step1Labels raw3811step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw3812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3812step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3812step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3812step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3812step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3812 raw3812Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw3812 raw3812Labels = mixedMoment B raw3812step0 raw3812step0Labels := by
      have hz : ∀ j, raw3812 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3812step0 = (fun i j => raw3812 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3812step0 raw3812; decide +kernel
      have hl : raw3812step0Labels = raw3812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3812 raw3812Labels permutation265 hz
    mixedMoment B raw3812step0 raw3812step0Labels = mixedMoment B raw3812step1 raw3812step1Labels := by
      have ha : raw3812step1 = (fun i j => raw3812step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3812step1 raw3812step0; decide +kernel
      have hl : raw3812step1Labels = raw3812step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3812step0 raw3812step0Labels permutation53 permutation7
    mixedMoment B raw3812step1 raw3812step1Labels = mixedMoment B raw3812step2 raw3812step2Labels := by
      have ha : raw3812step2 = -raw3812step1 := by apply Matrix.ext; change ∀ i j, raw3812step2 i j = -(raw3812step1 i j); unfold raw3812step2 raw3812step1; decide +kernel
      have hl : raw3812step2Labels = raw3812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3812step2 raw3812step2Labels = mixedMoment B raw3812step3 raw3812step3Labels := by
      have ha : raw3812step3 = raw3812step2 := by apply Matrix.ext; unfold raw3812step3 raw3812step2; decide +kernel
      have hl : raw3812step2Labels = labelEmbedding1 ∘ raw3812step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3812step2 raw3812step2Labels raw3812step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw3813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3813step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3813step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3813 raw3813Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw3813 raw3813Labels = mixedMoment B raw3813step0 raw3813step0Labels := by
      have hz : ∀ j, raw3813 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3813step0 = (fun i j => raw3813 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3813step0 raw3813; decide +kernel
      have hl : raw3813step0Labels = raw3813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3813 raw3813Labels permutation265 hz
    mixedMoment B raw3813step0 raw3813step0Labels = mixedMoment B raw3813step1 raw3813step1Labels := by
      have ha : raw3813step1 = (fun i j => raw3813step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3813step1 raw3813step0; decide +kernel
      have hl : raw3813step1Labels = raw3813step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3813step0 raw3813step0Labels permutation51 permutation7
    mixedMoment B raw3813step1 raw3813step1Labels = mixedMoment B raw3813step2 raw3813step2Labels := by
      have ha : raw3813step2 = -raw3813step1 := by apply Matrix.ext; change ∀ i j, raw3813step2 i j = -(raw3813step1 i j); unfold raw3813step2 raw3813step1; decide +kernel
      have hl : raw3813step2Labels = raw3813step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3813step2 raw3813step2Labels = mixedMoment B raw3813step3 raw3813step3Labels := by
      have ha : raw3813step3 = raw3813step2 := by apply Matrix.ext; unfold raw3813step3 raw3813step2; decide +kernel
      have hl : raw3813step2Labels = labelEmbedding1 ∘ raw3813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3813step2 raw3813step2Labels raw3813step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw3814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3814step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3814 raw3814Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw3814 raw3814Labels = mixedMoment B raw3814step0 raw3814step0Labels := by
      have ha : raw3814step0 = (fun i j => raw3814 (permutation649 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3814step0 raw3814; decide +kernel
      have hl : raw3814step0Labels = raw3814Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3814 raw3814Labels permutation649 permutation5
    mixedMoment B raw3814step0 raw3814step0Labels = mixedMoment B raw3814step1 raw3814step1Labels := by
      have ha : raw3814step1 = raw3814step0 := by apply Matrix.ext; unfold raw3814step1 raw3814step0; decide +kernel
      have hl : raw3814step0Labels = labelEmbedding1 ∘ raw3814step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3814step0 raw3814step0Labels raw3814step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2219 node2219Labels := by rfl

def raw3815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3815 raw3815Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw3815 raw3815Labels = mixedMoment B raw3815step0 raw3815step0Labels := by
      have hz : ∀ j, raw3815 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3815step0 = (fun i j => raw3815 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3815step0 raw3815; decide +kernel
      have hl : raw3815step0Labels = raw3815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3815 raw3815Labels permutation265 hz
    mixedMoment B raw3815step0 raw3815step0Labels = mixedMoment B raw3815step1 raw3815step1Labels := by
      have ha : raw3815step1 = (fun i j => raw3815step0 (permutation141 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3815step1 raw3815step0; decide +kernel
      have hl : raw3815step1Labels = raw3815step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3815step0 raw3815step0Labels permutation141 permutation5
    mixedMoment B raw3815step1 raw3815step1Labels = mixedMoment B raw3815step2 raw3815step2Labels := by
      have ha : raw3815step2 = raw3815step1 := by apply Matrix.ext; unfold raw3815step2 raw3815step1; decide +kernel
      have hl : raw3815step1Labels = labelEmbedding1 ∘ raw3815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3815step1 raw3815step1Labels raw3815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw3816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3816step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3816 raw3816Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw3816 raw3816Labels = mixedMoment B raw3816step0 raw3816step0Labels := by
      have hz : ∀ j, raw3816 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3816step0 = (fun i j => raw3816 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3816step0 raw3816; decide +kernel
      have hl : raw3816step0Labels = raw3816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3816 raw3816Labels permutation265 hz
    mixedMoment B raw3816step0 raw3816step0Labels = mixedMoment B raw3816step1 raw3816step1Labels := by
      have ha : raw3816step1 = (fun i j => raw3816step0 (permutation140 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3816step1 raw3816step0; decide +kernel
      have hl : raw3816step1Labels = raw3816step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3816step0 raw3816step0Labels permutation140 permutation5
    mixedMoment B raw3816step1 raw3816step1Labels = mixedMoment B raw3816step2 raw3816step2Labels := by
      have ha : raw3816step2 = raw3816step1 := by apply Matrix.ext; unfold raw3816step2 raw3816step1; decide +kernel
      have hl : raw3816step1Labels = labelEmbedding1 ∘ raw3816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3816step1 raw3816step1Labels raw3816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw3817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3817step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3817step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3817step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3817step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3817 raw3817Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw3817 raw3817Labels = mixedMoment B raw3817step0 raw3817step0Labels := by
      have hz : ∀ j, raw3817 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3817step0 = (fun i j => raw3817 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3817step0 raw3817; decide +kernel
      have hl : raw3817step0Labels = raw3817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3817 raw3817Labels permutation265 hz
    mixedMoment B raw3817step0 raw3817step0Labels = mixedMoment B raw3817step1 raw3817step1Labels := by
      have ha : raw3817step1 = (fun i j => raw3817step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3817step1 raw3817step0; decide +kernel
      have hl : raw3817step1Labels = raw3817step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3817step0 raw3817step0Labels permutation51 permutation7
    mixedMoment B raw3817step1 raw3817step1Labels = mixedMoment B raw3817step2 raw3817step2Labels := by
      have ha : raw3817step2 = -raw3817step1 := by apply Matrix.ext; change ∀ i j, raw3817step2 i j = -(raw3817step1 i j); unfold raw3817step2 raw3817step1; decide +kernel
      have hl : raw3817step2Labels = raw3817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3817step2 raw3817step2Labels = mixedMoment B raw3817step3 raw3817step3Labels := by
      have ha : raw3817step3 = raw3817step2 := by apply Matrix.ext; unfold raw3817step3 raw3817step2; decide +kernel
      have hl : raw3817step2Labels = labelEmbedding1 ∘ raw3817step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3817step2 raw3817step2Labels raw3817step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw3818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3818step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3818step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3818step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3818 raw3818Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw3818 raw3818Labels = mixedMoment B raw3818step0 raw3818step0Labels := by
      have hz : ∀ j, raw3818 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3818step0 = (fun i j => raw3818 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3818step0 raw3818; decide +kernel
      have hl : raw3818step0Labels = raw3818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3818 raw3818Labels permutation265 hz
    mixedMoment B raw3818step0 raw3818step0Labels = mixedMoment B raw3818step1 raw3818step1Labels := by
      have ha : raw3818step1 = (fun i j => raw3818step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3818step1 raw3818step0; decide +kernel
      have hl : raw3818step1Labels = raw3818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3818step0 raw3818step0Labels permutation50 permutation7
    mixedMoment B raw3818step1 raw3818step1Labels = mixedMoment B raw3818step2 raw3818step2Labels := by
      have ha : raw3818step2 = -raw3818step1 := by apply Matrix.ext; change ∀ i j, raw3818step2 i j = -(raw3818step1 i j); unfold raw3818step2 raw3818step1; decide +kernel
      have hl : raw3818step2Labels = raw3818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3818step2 raw3818step2Labels = mixedMoment B raw3818step3 raw3818step3Labels := by
      have ha : raw3818step3 = raw3818step2 := by apply Matrix.ext; unfold raw3818step3 raw3818step2; decide +kernel
      have hl : raw3818step2Labels = labelEmbedding1 ∘ raw3818step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3818step2 raw3818step2Labels raw3818step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw3819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3819step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3819 raw3819Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw3819 raw3819Labels = mixedMoment B raw3819step0 raw3819step0Labels := by
      have ha : raw3819step0 = (fun i j => raw3819 (permutation668 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3819step0 raw3819; decide +kernel
      have hl : raw3819step0Labels = raw3819Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3819 raw3819Labels permutation668 permutation5
    mixedMoment B raw3819step0 raw3819step0Labels = mixedMoment B raw3819step1 raw3819step1Labels := by
      have ha : raw3819step1 = raw3819step0 := by apply Matrix.ext; unfold raw3819step1 raw3819step0; decide +kernel
      have hl : raw3819step0Labels = labelEmbedding1 ∘ raw3819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3819step0 raw3819step0Labels raw3819step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2219 node2219Labels := by rfl

def raw3820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3820step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3820 raw3820Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw3820 raw3820Labels = mixedMoment B raw3820step0 raw3820step0Labels := by
      have hz : ∀ j, raw3820 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3820step0 = (fun i j => raw3820 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3820step0 raw3820; decide +kernel
      have hl : raw3820step0Labels = raw3820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3820 raw3820Labels permutation265 hz
    mixedMoment B raw3820step0 raw3820step0Labels = mixedMoment B raw3820step1 raw3820step1Labels := by
      have ha : raw3820step1 = (fun i j => raw3820step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3820step1 raw3820step0; decide +kernel
      have hl : raw3820step1Labels = raw3820step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3820step0 raw3820step0Labels permutation147 permutation5
    mixedMoment B raw3820step1 raw3820step1Labels = mixedMoment B raw3820step2 raw3820step2Labels := by
      have ha : raw3820step2 = raw3820step1 := by apply Matrix.ext; unfold raw3820step2 raw3820step1; decide +kernel
      have hl : raw3820step1Labels = labelEmbedding1 ∘ raw3820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3820step1 raw3820step1Labels raw3820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw3821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3821step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3821step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3821 raw3821Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw3821 raw3821Labels = mixedMoment B raw3821step0 raw3821step0Labels := by
      have hz : ∀ j, raw3821 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3821step0 = (fun i j => raw3821 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3821step0 raw3821; decide +kernel
      have hl : raw3821step0Labels = raw3821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3821 raw3821Labels permutation265 hz
    mixedMoment B raw3821step0 raw3821step0Labels = mixedMoment B raw3821step1 raw3821step1Labels := by
      have ha : raw3821step1 = (fun i j => raw3821step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3821step1 raw3821step0; decide +kernel
      have hl : raw3821step1Labels = raw3821step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3821step0 raw3821step0Labels permutation146 permutation5
    mixedMoment B raw3821step1 raw3821step1Labels = mixedMoment B raw3821step2 raw3821step2Labels := by
      have ha : raw3821step2 = raw3821step1 := by apply Matrix.ext; unfold raw3821step2 raw3821step1; decide +kernel
      have hl : raw3821step1Labels = labelEmbedding1 ∘ raw3821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3821step1 raw3821step1Labels raw3821step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw3822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3822step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3822step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3822step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3822step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3822step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3822 raw3822Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw3822 raw3822Labels = mixedMoment B raw3822step0 raw3822step0Labels := by
      have hz : ∀ j, raw3822 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3822step0 = (fun i j => raw3822 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3822step0 raw3822; decide +kernel
      have hl : raw3822step0Labels = raw3822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3822 raw3822Labels permutation265 hz
    mixedMoment B raw3822step0 raw3822step0Labels = mixedMoment B raw3822step1 raw3822step1Labels := by
      have ha : raw3822step1 = (fun i j => raw3822step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3822step1 raw3822step0; decide +kernel
      have hl : raw3822step1Labels = raw3822step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3822step0 raw3822step0Labels permutation50 permutation7
    mixedMoment B raw3822step1 raw3822step1Labels = mixedMoment B raw3822step2 raw3822step2Labels := by
      have ha : raw3822step2 = -raw3822step1 := by apply Matrix.ext; change ∀ i j, raw3822step2 i j = -(raw3822step1 i j); unfold raw3822step2 raw3822step1; decide +kernel
      have hl : raw3822step2Labels = raw3822step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3822step2 raw3822step2Labels = mixedMoment B raw3822step3 raw3822step3Labels := by
      have ha : raw3822step3 = raw3822step2 := by apply Matrix.ext; unfold raw3822step3 raw3822step2; decide +kernel
      have hl : raw3822step2Labels = labelEmbedding1 ∘ raw3822step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3822step2 raw3822step2Labels raw3822step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw3823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3823step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw3823step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw3823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3823 raw3823Labels = mixedMoment B node846 node846Labels := by
  calc
    mixedMoment B raw3823 raw3823Labels = mixedMoment B raw3823step0 raw3823step0Labels := by
      have hz : ∀ j, raw3823 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3823step0 = (fun i j => raw3823 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3823step0 raw3823; decide +kernel
      have hl : raw3823step0Labels = raw3823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3823 raw3823Labels permutation265 hz
    mixedMoment B raw3823step0 raw3823step0Labels = mixedMoment B raw3823step1 raw3823step1Labels := by
      have ha : raw3823step1 = (fun i j => raw3823step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3823step1 raw3823step0; decide +kernel
      have hl : raw3823step1Labels = raw3823step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3823step0 raw3823step0Labels permutation137 permutation5
    mixedMoment B raw3823step1 raw3823step1Labels = mixedMoment B raw3823step2 raw3823step2Labels := by
      have ha : raw3823step2 = raw3823step1 := by apply Matrix.ext; unfold raw3823step2 raw3823step1; decide +kernel
      have hl : raw3823step1Labels = labelEmbedding1 ∘ raw3823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3823step1 raw3823step1Labels raw3823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node846 node846Labels := by rfl

def raw3824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3824 raw3824Labels = mixedMoment B node833 node833Labels := by
  calc
    mixedMoment B raw3824 raw3824Labels = mixedMoment B raw3824step0 raw3824step0Labels := by
      have ha : raw3824step0 = (fun i j => raw3824 (permutation595 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3824step0 raw3824; decide +kernel
      have hl : raw3824step0Labels = raw3824Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3824 raw3824Labels permutation595 permutation5
    mixedMoment B raw3824step0 raw3824step0Labels = mixedMoment B raw3824step1 raw3824step1Labels := by
      have ha : raw3824step1 = raw3824step0 := by apply Matrix.ext; unfold raw3824step1 raw3824step0; decide +kernel
      have hl : raw3824step0Labels = labelEmbedding1 ∘ raw3824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3824step0 raw3824step0Labels raw3824step1Labels labelEmbedding1 hl
    _ = mixedMoment B node833 node833Labels := by rfl

def raw3825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3825step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3825step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3825 raw3825Labels = mixedMoment B node834 node834Labels := by
  calc
    mixedMoment B raw3825 raw3825Labels = mixedMoment B raw3825step0 raw3825step0Labels := by
      have hz : ∀ j, raw3825 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3825step0 = (fun i j => raw3825 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3825step0 raw3825; decide +kernel
      have hl : raw3825step0Labels = raw3825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3825 raw3825Labels permutation265 hz
    mixedMoment B raw3825step0 raw3825step0Labels = mixedMoment B raw3825step1 raw3825step1Labels := by
      have ha : raw3825step1 = (fun i j => raw3825step0 (permutation131 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3825step1 raw3825step0; decide +kernel
      have hl : raw3825step1Labels = raw3825step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3825step0 raw3825step0Labels permutation131 permutation5
    mixedMoment B raw3825step1 raw3825step1Labels = mixedMoment B raw3825step2 raw3825step2Labels := by
      have ha : raw3825step2 = raw3825step1 := by apply Matrix.ext; unfold raw3825step2 raw3825step1; decide +kernel
      have hl : raw3825step1Labels = labelEmbedding1 ∘ raw3825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3825step1 raw3825step1Labels raw3825step2Labels labelEmbedding1 hl
    _ = mixedMoment B node834 node834Labels := by rfl

def raw3826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3826step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3826 raw3826Labels = mixedMoment B node834 node834Labels := by
  calc
    mixedMoment B raw3826 raw3826Labels = mixedMoment B raw3826step0 raw3826step0Labels := by
      have hz : ∀ j, raw3826 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3826step0 = (fun i j => raw3826 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3826step0 raw3826; decide +kernel
      have hl : raw3826step0Labels = raw3826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3826 raw3826Labels permutation265 hz
    mixedMoment B raw3826step0 raw3826step0Labels = mixedMoment B raw3826step1 raw3826step1Labels := by
      have ha : raw3826step1 = (fun i j => raw3826step0 (permutation129 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3826step1 raw3826step0; decide +kernel
      have hl : raw3826step1Labels = raw3826step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3826step0 raw3826step0Labels permutation129 permutation5
    mixedMoment B raw3826step1 raw3826step1Labels = mixedMoment B raw3826step2 raw3826step2Labels := by
      have ha : raw3826step2 = raw3826step1 := by apply Matrix.ext; unfold raw3826step2 raw3826step1; decide +kernel
      have hl : raw3826step1Labels = labelEmbedding1 ∘ raw3826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3826step1 raw3826step1Labels raw3826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node834 node834Labels := by rfl

def raw3827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw3827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw3827step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3827step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw3827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3827 raw3827Labels = mixedMoment B node834 node834Labels := by
  calc
    mixedMoment B raw3827 raw3827Labels = mixedMoment B raw3827step0 raw3827step0Labels := by
      have hz : ∀ j, raw3827 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3827step0 = (fun i j => raw3827 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3827step0 raw3827; decide +kernel
      have hl : raw3827step0Labels = raw3827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3827 raw3827Labels permutation265 hz
    mixedMoment B raw3827step0 raw3827step0Labels = mixedMoment B raw3827step1 raw3827step1Labels := by
      have ha : raw3827step1 = (fun i j => raw3827step0 (permutation128 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3827step1 raw3827step0; decide +kernel
      have hl : raw3827step1Labels = raw3827step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3827step0 raw3827step0Labels permutation128 permutation5
    mixedMoment B raw3827step1 raw3827step1Labels = mixedMoment B raw3827step2 raw3827step2Labels := by
      have ha : raw3827step2 = raw3827step1 := by apply Matrix.ext; unfold raw3827step2 raw3827step1; decide +kernel
      have hl : raw3827step1Labels = labelEmbedding1 ∘ raw3827step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3827step1 raw3827step1Labels raw3827step2Labels labelEmbedding1 hl
    _ = mixedMoment B node834 node834Labels := by rfl

def raw3828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3828 raw3828Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw3828 raw3828Labels = mixedMoment B raw3828step0 raw3828step0Labels := by
      have hz : ∀ j, raw3828 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3828step0 = (fun i j => raw3828 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3828step0 raw3828; decide +kernel
      have hl : raw3828step0Labels = raw3828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3828 raw3828Labels permutation265 hz
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw3829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3829 raw3829Labels = mixedMoment B node3155 node3155Labels := by
  calc
    mixedMoment B raw3829 raw3829Labels = mixedMoment B raw3829step0 raw3829step0Labels := by
      have ha : raw3829step0 = (fun i j => raw3829 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3829step0 raw3829; decide +kernel
      have hl : raw3829step0Labels = raw3829Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3829 raw3829Labels permutation590 permutation4
    _ = mixedMoment B node3155 node3155Labels := by rfl

def raw3830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3830 raw3830Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw3830 raw3830Labels = mixedMoment B raw3830step0 raw3830step0Labels := by
      have hz : ∀ j, raw3830 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3830step0 = (fun i j => raw3830 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3830step0 raw3830; decide +kernel
      have hl : raw3830step0Labels = raw3830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3830 raw3830Labels permutation265 hz
    mixedMoment B raw3830step0 raw3830step0Labels = mixedMoment B raw3830step1 raw3830step1Labels := by
      have ha : raw3830step1 = (fun i j => raw3830step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3830step1 raw3830step0; decide +kernel
      have hl : raw3830step1Labels = raw3830step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3830step0 raw3830step0Labels permutation131 permutation4
    _ = mixedMoment B node3158 node3158Labels := by rfl

def raw3831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3831 raw3831Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw3831 raw3831Labels = mixedMoment B raw3831step0 raw3831step0Labels := by
      have hz : ∀ j, raw3831 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3831step0 = (fun i j => raw3831 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3831step0 raw3831; decide +kernel
      have hl : raw3831step0Labels = raw3831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3831 raw3831Labels permutation265 hz
    mixedMoment B raw3831step0 raw3831step0Labels = mixedMoment B raw3831step1 raw3831step1Labels := by
      have ha : raw3831step1 = (fun i j => raw3831step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3831step1 raw3831step0; decide +kernel
      have hl : raw3831step1Labels = raw3831step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3831step0 raw3831step0Labels permutation129 permutation4
    _ = mixedMoment B node3158 node3158Labels := by rfl

def raw3832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3832 raw3832Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw3832 raw3832Labels = mixedMoment B raw3832step0 raw3832step0Labels := by
      have hz : ∀ j, raw3832 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3832step0 = (fun i j => raw3832 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3832step0 raw3832; decide +kernel
      have hl : raw3832step0Labels = raw3832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3832 raw3832Labels permutation265 hz
    mixedMoment B raw3832step0 raw3832step0Labels = mixedMoment B raw3832step1 raw3832step1Labels := by
      have ha : raw3832step1 = (fun i j => raw3832step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3832step1 raw3832step0; decide +kernel
      have hl : raw3832step1Labels = raw3832step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3832step0 raw3832step0Labels permutation128 permutation4
    _ = mixedMoment B node3158 node3158Labels := by rfl

def raw3833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3833 raw3833Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw3833 raw3833Labels = mixedMoment B raw3833step0 raw3833step0Labels := by
      have hz : ∀ j, raw3833 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3833step0 = (fun i j => raw3833 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3833step0 raw3833; decide +kernel
      have hl : raw3833step0Labels = raw3833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3833 raw3833Labels permutation265 hz
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw3834 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw3834Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3834step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw3834step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3834step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw3834step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3834 raw3834Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3834 raw3834Labels = mixedMoment B raw3834step0 raw3834step0Labels := by
      have hz : ∀ j, raw3834 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3834step0 = (fun i j => raw3834 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3834step0 raw3834; decide +kernel
      have hl : raw3834step0Labels = raw3834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3834 raw3834Labels permutation590 hz
    mixedMoment B raw3834step0 raw3834step0Labels = mixedMoment B raw3834step1 raw3834step1Labels := by
      have hz : ∀ j, raw3834step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3834step1 = (fun i j => raw3834step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3834step1 raw3834step0; decide +kernel
      have hl : raw3834step1Labels = raw3834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3834step0 raw3834step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw3835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3835 raw3835Labels = mixedMoment B node1014 node1014Labels := by
  calc
    mixedMoment B raw3835 raw3835Labels = mixedMoment B raw3835step0 raw3835step0Labels := by
      have ha : raw3835step0 = (fun i j => raw3835 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3835step0 raw3835; decide +kernel
      have hl : raw3835step0Labels = raw3835Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3835 raw3835Labels permutation184 permutation2
    _ = mixedMoment B node1014 node1014Labels := by rfl

def raw3836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3836 raw3836Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw3836 raw3836Labels = mixedMoment B raw3836step0 raw3836step0Labels := by
      have hz : ∀ j, raw3836 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3836step0 = (fun i j => raw3836 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3836step0 raw3836; decide +kernel
      have hl : raw3836step0Labels = raw3836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3836 raw3836Labels permutation265 hz
    mixedMoment B raw3836step0 raw3836step0Labels = mixedMoment B raw3836step1 raw3836step1Labels := by
      have ha : raw3836step1 = (fun i j => raw3836step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3836step1 raw3836step0; decide +kernel
      have hl : raw3836step1Labels = raw3836step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3836step0 raw3836step0Labels permutation40 permutation2
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw3837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3837 raw3837Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw3837 raw3837Labels = mixedMoment B raw3837step0 raw3837step0Labels := by
      have hz : ∀ j, raw3837 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3837step0 = (fun i j => raw3837 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3837step0 raw3837; decide +kernel
      have hl : raw3837step0Labels = raw3837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3837 raw3837Labels permutation265 hz
    mixedMoment B raw3837step0 raw3837step0Labels = mixedMoment B raw3837step1 raw3837step1Labels := by
      have ha : raw3837step1 = (fun i j => raw3837step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3837step1 raw3837step0; decide +kernel
      have hl : raw3837step1Labels = raw3837step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3837step0 raw3837step0Labels permutation34 permutation2
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw3838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3838 raw3838Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw3838 raw3838Labels = mixedMoment B raw3838step0 raw3838step0Labels := by
      have hz : ∀ j, raw3838 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3838step0 = (fun i j => raw3838 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3838step0 raw3838; decide +kernel
      have hl : raw3838step0Labels = raw3838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3838 raw3838Labels permutation265 hz
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw3839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3839 raw3839Labels = mixedMoment B node1016 node1016Labels := by
  calc
    mixedMoment B raw3839 raw3839Labels = mixedMoment B raw3839step0 raw3839step0Labels := by
      have hz : ∀ j, raw3839 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3839step0 = (fun i j => raw3839 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3839step0 raw3839; decide +kernel
      have hl : raw3839step0Labels = raw3839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3839 raw3839Labels permutation265 hz
    _ = mixedMoment B node1016 node1016Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
