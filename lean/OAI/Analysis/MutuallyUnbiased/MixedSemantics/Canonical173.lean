import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22144 raw22144Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw22144 raw22144Labels = mixedMoment B raw22144step0 raw22144step0Labels := by
      have hz : ∀ j, raw22144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22144step0 = (fun i j => raw22144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22144step0 raw22144; decide +kernel
      have hl : raw22144step0Labels = raw22144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22144 raw22144Labels permutation434 hz
    mixedMoment B raw22144step0 raw22144step0Labels = mixedMoment B raw22144step1 raw22144step1Labels := by
      have ha : raw22144step1 = (fun i j => raw22144step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22144step1 raw22144step0; decide +kernel
      have hl : raw22144step1Labels = raw22144step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22144step0 raw22144step0Labels permutation34 permutation2
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw22145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22145 raw22145Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw22145 raw22145Labels = mixedMoment B raw22145step0 raw22145step0Labels := by
      have hz : ∀ j, raw22145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22145step0 = (fun i j => raw22145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22145step0 raw22145; decide +kernel
      have hl : raw22145step0Labels = raw22145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22145 raw22145Labels permutation434 hz
    _ = mixedMoment B node4264 node4264Labels := by rfl

def raw22146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22146 raw22146Labels = mixedMoment B node4101 node4101Labels := by
  calc
    mixedMoment B raw22146 raw22146Labels = mixedMoment B raw22146step0 raw22146step0Labels := by
      have hz : ∀ j, raw22146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22146step0 = (fun i j => raw22146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22146step0 raw22146; decide +kernel
      have hl : raw22146step0Labels = raw22146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22146 raw22146Labels permutation346 hz
    _ = mixedMoment B node4101 node4101Labels := by rfl

def raw22147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22147 raw22147Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw22147 raw22147Labels = mixedMoment B raw22147step0 raw22147step0Labels := by
      have hz : ∀ j, raw22147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22147step0 = (fun i j => raw22147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22147step0 raw22147; decide +kernel
      have hl : raw22147step0Labels = raw22147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22147 raw22147Labels permutation346 hz
    _ = mixedMoment B node4233 node4233Labels := by rfl

def raw22148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22148 raw22148Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw22148 raw22148Labels = mixedMoment B raw22148step0 raw22148step0Labels := by
      have ha : raw22148step0 = (fun i j => raw22148 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22148step0 raw22148; decide +kernel
      have hl : raw22148step0Labels = raw22148Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22148 raw22148Labels permutation176 permutation2
    _ = mixedMoment B node4196 node4196Labels := by rfl

def raw22149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22149 raw22149Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw22149 raw22149Labels = mixedMoment B raw22149step0 raw22149step0Labels := by
      have hz : ∀ j, raw22149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22149step0 = (fun i j => raw22149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22149step0 raw22149; decide +kernel
      have hl : raw22149step0Labels = raw22149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22149 raw22149Labels permutation346 hz
    mixedMoment B raw22149step0 raw22149step0Labels = mixedMoment B raw22149step1 raw22149step1Labels := by
      have ha : raw22149step1 = (fun i j => raw22149step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22149step1 raw22149step0; decide +kernel
      have hl : raw22149step1Labels = raw22149step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22149step0 raw22149step0Labels permutation34 permutation2
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw22150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22150 raw22150Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw22150 raw22150Labels = mixedMoment B raw22150step0 raw22150step0Labels := by
      have hz : ∀ j, raw22150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22150step0 = (fun i j => raw22150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22150step0 raw22150; decide +kernel
      have hl : raw22150step0Labels = raw22150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22150 raw22150Labels permutation346 hz
    _ = mixedMoment B node4264 node4264Labels := by rfl

def raw22151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22151 raw22151Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw22151 raw22151Labels = mixedMoment B raw22151step0 raw22151step0Labels := by
      have hz : ∀ j, raw22151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22151step0 = (fun i j => raw22151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22151step0 raw22151; decide +kernel
      have hl : raw22151step0Labels = raw22151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22151 raw22151Labels permutation434 hz
    mixedMoment B raw22151step0 raw22151step0Labels = mixedMoment B raw22151step1 raw22151step1Labels := by
      have hz : ∀ j, raw22151step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22151step1 = (fun i j => raw22151step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22151step1 raw22151step0; decide +kernel
      have hl : raw22151step1Labels = raw22151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22151step0 raw22151step0Labels permutation80 hz
    _ = mixedMoment B node4110 node4110Labels := by rfl

def raw22152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22152 raw22152Labels = mixedMoment B node4242 node4242Labels := by
  calc
    mixedMoment B raw22152 raw22152Labels = mixedMoment B raw22152step0 raw22152step0Labels := by
      have hz : ∀ j, raw22152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22152step0 = (fun i j => raw22152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22152step0 raw22152; decide +kernel
      have hl : raw22152step0Labels = raw22152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22152 raw22152Labels permutation434 hz
    mixedMoment B raw22152step0 raw22152step0Labels = mixedMoment B raw22152step1 raw22152step1Labels := by
      have hz : ∀ j, raw22152step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22152step1 = (fun i j => raw22152step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22152step1 raw22152step0; decide +kernel
      have hl : raw22152step1Labels = raw22152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22152step0 raw22152step0Labels permutation80 hz
    _ = mixedMoment B node4242 node4242Labels := by rfl

def raw22153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22153 raw22153Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw22153 raw22153Labels = mixedMoment B raw22153step0 raw22153step0Labels := by
      have hz : ∀ j, raw22153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22153step0 = (fun i j => raw22153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22153step0 raw22153; decide +kernel
      have hl : raw22153step0Labels = raw22153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22153 raw22153Labels permutation434 hz
    mixedMoment B raw22153step0 raw22153step0Labels = mixedMoment B raw22153step1 raw22153step1Labels := by
      have ha : raw22153step1 = (fun i j => raw22153step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22153step1 raw22153step0; decide +kernel
      have hl : raw22153step1Labels = raw22153step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22153step0 raw22153step0Labels permutation38 permutation2
    _ = mixedMoment B node4204 node4204Labels := by rfl

def raw22154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22154 raw22154Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw22154 raw22154Labels = mixedMoment B raw22154step0 raw22154step0Labels := by
      have hz : ∀ j, raw22154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22154step0 = (fun i j => raw22154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22154step0 raw22154; decide +kernel
      have hl : raw22154step0Labels = raw22154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22154 raw22154Labels permutation346 hz
    mixedMoment B raw22154step0 raw22154step0Labels = mixedMoment B raw22154step1 raw22154step1Labels := by
      have ha : raw22154step1 = (fun i j => raw22154step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22154step1 raw22154step0; decide +kernel
      have hl : raw22154step1Labels = raw22154step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22154step0 raw22154step0Labels permutation38 permutation2
    _ = mixedMoment B node4204 node4204Labels := by rfl

def raw22155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22155 raw22155Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw22155 raw22155Labels = mixedMoment B raw22155step0 raw22155step0Labels := by
      have hz : ∀ j, raw22155 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22155step0 = (fun i j => raw22155 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22155step0 raw22155; decide +kernel
      have hl : raw22155step0Labels = raw22155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22155 raw22155Labels permutation434 hz
    mixedMoment B raw22155step0 raw22155step0Labels = mixedMoment B raw22155step1 raw22155step1Labels := by
      have hz : ∀ j, raw22155step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22155step1 = (fun i j => raw22155step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22155step1 raw22155step0; decide +kernel
      have hl : raw22155step1Labels = raw22155step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22155step0 raw22155step0Labels permutation80 hz
    _ = mixedMoment B node4273 node4273Labels := by rfl

def raw22156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22156 raw22156Labels = mixedMoment B node4108 node4108Labels := by
  calc
    mixedMoment B raw22156 raw22156Labels = mixedMoment B raw22156step0 raw22156step0Labels := by
      have hz : ∀ j, raw22156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22156step0 = (fun i j => raw22156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22156step0 raw22156; decide +kernel
      have hl : raw22156step0Labels = raw22156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22156 raw22156Labels permutation434 hz
    mixedMoment B raw22156step0 raw22156step0Labels = mixedMoment B raw22156step1 raw22156step1Labels := by
      have hz : ∀ j, raw22156step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22156step1 = (fun i j => raw22156step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22156step1 raw22156step0; decide +kernel
      have hl : raw22156step1Labels = raw22156step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22156step0 raw22156step0Labels permutation80 hz
    _ = mixedMoment B node4108 node4108Labels := by rfl

def raw22157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22157 raw22157Labels = mixedMoment B node4240 node4240Labels := by
  calc
    mixedMoment B raw22157 raw22157Labels = mixedMoment B raw22157step0 raw22157step0Labels := by
      have hz : ∀ j, raw22157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22157step0 = (fun i j => raw22157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22157step0 raw22157; decide +kernel
      have hl : raw22157step0Labels = raw22157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22157 raw22157Labels permutation434 hz
    mixedMoment B raw22157step0 raw22157step0Labels = mixedMoment B raw22157step1 raw22157step1Labels := by
      have hz : ∀ j, raw22157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22157step1 = (fun i j => raw22157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22157step1 raw22157step0; decide +kernel
      have hl : raw22157step1Labels = raw22157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22157step0 raw22157step0Labels permutation80 hz
    _ = mixedMoment B node4240 node4240Labels := by rfl

def raw22158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22158 raw22158Labels = mixedMoment B node4202 node4202Labels := by
  calc
    mixedMoment B raw22158 raw22158Labels = mixedMoment B raw22158step0 raw22158step0Labels := by
      have hz : ∀ j, raw22158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22158step0 = (fun i j => raw22158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22158step0 raw22158; decide +kernel
      have hl : raw22158step0Labels = raw22158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22158 raw22158Labels permutation434 hz
    mixedMoment B raw22158step0 raw22158step0Labels = mixedMoment B raw22158step1 raw22158step1Labels := by
      have ha : raw22158step1 = (fun i j => raw22158step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22158step1 raw22158step0; decide +kernel
      have hl : raw22158step1Labels = raw22158step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22158step0 raw22158step0Labels permutation38 permutation2
    _ = mixedMoment B node4202 node4202Labels := by rfl

def raw22159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22159 raw22159Labels = mixedMoment B node4202 node4202Labels := by
  calc
    mixedMoment B raw22159 raw22159Labels = mixedMoment B raw22159step0 raw22159step0Labels := by
      have hz : ∀ j, raw22159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22159step0 = (fun i j => raw22159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22159step0 raw22159; decide +kernel
      have hl : raw22159step0Labels = raw22159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22159 raw22159Labels permutation346 hz
    mixedMoment B raw22159step0 raw22159step0Labels = mixedMoment B raw22159step1 raw22159step1Labels := by
      have ha : raw22159step1 = (fun i j => raw22159step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22159step1 raw22159step0; decide +kernel
      have hl : raw22159step1Labels = raw22159step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22159step0 raw22159step0Labels permutation38 permutation2
    _ = mixedMoment B node4202 node4202Labels := by rfl

def raw22160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw22160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22160 raw22160Labels = mixedMoment B node4257 node4257Labels := by
  calc
    mixedMoment B raw22160 raw22160Labels = mixedMoment B raw22160step0 raw22160step0Labels := by
      have hz : ∀ j, raw22160 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22160step0 = (fun i j => raw22160 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22160step0 raw22160; decide +kernel
      have hl : raw22160step0Labels = raw22160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22160 raw22160Labels permutation434 hz
    mixedMoment B raw22160step0 raw22160step0Labels = mixedMoment B raw22160step1 raw22160step1Labels := by
      have hz : ∀ j, raw22160step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22160step1 = (fun i j => raw22160step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22160step1 raw22160step0; decide +kernel
      have hl : raw22160step1Labels = raw22160step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22160step0 raw22160step0Labels permutation80 hz
    _ = mixedMoment B node4257 node4257Labels := by rfl

def raw22161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22161step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22161step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22161step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22161step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22161step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22161step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22161step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22161step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22161 raw22161Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw22161 raw22161Labels = mixedMoment B raw22161step0 raw22161step0Labels := by
      have hz : ∀ j, raw22161 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22161step0 = (fun i j => raw22161 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22161step0 raw22161; decide +kernel
      have hl : raw22161step0Labels = raw22161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22161 raw22161Labels permutation434 hz
    mixedMoment B raw22161step0 raw22161step0Labels = mixedMoment B raw22161step1 raw22161step1Labels := by
      have hz : ∀ j, raw22161step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22161step1 = (fun i j => raw22161step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22161step1 raw22161step0; decide +kernel
      have hl : raw22161step1Labels = raw22161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22161step0 raw22161step0Labels permutation80 hz
    mixedMoment B raw22161step1 raw22161step1Labels = mixedMoment B raw22161step2 raw22161step2Labels := by
      have ha : raw22161step2 = (fun i j => raw22161step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22161step2 raw22161step1; decide +kernel
      have hl : raw22161step2Labels = raw22161step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22161step1 raw22161step1Labels permutation8 permutation7
    mixedMoment B raw22161step2 raw22161step2Labels = mixedMoment B raw22161step3 raw22161step3Labels := by
      have ha : raw22161step3 = -raw22161step2 := by apply Matrix.ext; change ∀ i j, raw22161step3 i j = -(raw22161step2 i j); unfold raw22161step3 raw22161step2; decide +kernel
      have hl : raw22161step3Labels = raw22161step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22161step3 raw22161step3Labels = mixedMoment B raw22161step4 raw22161step4Labels := by
      have ha : raw22161step4 = raw22161step3 := by apply Matrix.ext; unfold raw22161step4 raw22161step3; decide +kernel
      have hl : raw22161step3Labels = labelEmbedding1 ∘ raw22161step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22161step3 raw22161step3Labels raw22161step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1074 node1074Labels := by rfl

def raw22162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22162step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22162step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22162step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22162 raw22162Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw22162 raw22162Labels = mixedMoment B raw22162step0 raw22162step0Labels := by
      have hz : ∀ j, raw22162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22162step0 = (fun i j => raw22162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22162step0 raw22162; decide +kernel
      have hl : raw22162step0Labels = raw22162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22162 raw22162Labels permutation434 hz
    mixedMoment B raw22162step0 raw22162step0Labels = mixedMoment B raw22162step1 raw22162step1Labels := by
      have ha : raw22162step1 = (fun i j => raw22162step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22162step1 raw22162step0; decide +kernel
      have hl : raw22162step1Labels = raw22162step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22162step0 raw22162step0Labels permutation38 permutation7
    mixedMoment B raw22162step1 raw22162step1Labels = mixedMoment B raw22162step2 raw22162step2Labels := by
      have ha : raw22162step2 = -raw22162step1 := by apply Matrix.ext; change ∀ i j, raw22162step2 i j = -(raw22162step1 i j); unfold raw22162step2 raw22162step1; decide +kernel
      have hl : raw22162step2Labels = raw22162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22162step2 raw22162step2Labels = mixedMoment B raw22162step3 raw22162step3Labels := by
      have ha : raw22162step3 = raw22162step2 := by apply Matrix.ext; unfold raw22162step3 raw22162step2; decide +kernel
      have hl : raw22162step2Labels = labelEmbedding1 ∘ raw22162step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22162step2 raw22162step2Labels raw22162step3Labels labelEmbedding1 hl
    _ = mixedMoment B node999 node999Labels := by rfl

def raw22163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22163step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22163step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22163step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22163step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22163 raw22163Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw22163 raw22163Labels = mixedMoment B raw22163step0 raw22163step0Labels := by
      have hz : ∀ j, raw22163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22163step0 = (fun i j => raw22163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22163step0 raw22163; decide +kernel
      have hl : raw22163step0Labels = raw22163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22163 raw22163Labels permutation346 hz
    mixedMoment B raw22163step0 raw22163step0Labels = mixedMoment B raw22163step1 raw22163step1Labels := by
      have ha : raw22163step1 = (fun i j => raw22163step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22163step1 raw22163step0; decide +kernel
      have hl : raw22163step1Labels = raw22163step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22163step0 raw22163step0Labels permutation38 permutation7
    mixedMoment B raw22163step1 raw22163step1Labels = mixedMoment B raw22163step2 raw22163step2Labels := by
      have ha : raw22163step2 = -raw22163step1 := by apply Matrix.ext; change ∀ i j, raw22163step2 i j = -(raw22163step1 i j); unfold raw22163step2 raw22163step1; decide +kernel
      have hl : raw22163step2Labels = raw22163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22163step2 raw22163step2Labels = mixedMoment B raw22163step3 raw22163step3Labels := by
      have ha : raw22163step3 = raw22163step2 := by apply Matrix.ext; unfold raw22163step3 raw22163step2; decide +kernel
      have hl : raw22163step2Labels = labelEmbedding1 ∘ raw22163step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22163step2 raw22163step2Labels raw22163step3Labels labelEmbedding1 hl
    _ = mixedMoment B node999 node999Labels := by rfl

def raw22164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22164step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22164step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22164step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22164step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22164step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22164step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22164step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22164step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22164 raw22164Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw22164 raw22164Labels = mixedMoment B raw22164step0 raw22164step0Labels := by
      have hz : ∀ j, raw22164 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22164step0 = (fun i j => raw22164 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22164step0 raw22164; decide +kernel
      have hl : raw22164step0Labels = raw22164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22164 raw22164Labels permutation434 hz
    mixedMoment B raw22164step0 raw22164step0Labels = mixedMoment B raw22164step1 raw22164step1Labels := by
      have hz : ∀ j, raw22164step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22164step1 = (fun i j => raw22164step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22164step1 raw22164step0; decide +kernel
      have hl : raw22164step1Labels = raw22164step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22164step0 raw22164step0Labels permutation80 hz
    mixedMoment B raw22164step1 raw22164step1Labels = mixedMoment B raw22164step2 raw22164step2Labels := by
      have ha : raw22164step2 = (fun i j => raw22164step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22164step2 raw22164step1; decide +kernel
      have hl : raw22164step2Labels = raw22164step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22164step1 raw22164step1Labels permutation8 permutation7
    mixedMoment B raw22164step2 raw22164step2Labels = mixedMoment B raw22164step3 raw22164step3Labels := by
      have ha : raw22164step3 = -raw22164step2 := by apply Matrix.ext; change ∀ i j, raw22164step3 i j = -(raw22164step2 i j); unfold raw22164step3 raw22164step2; decide +kernel
      have hl : raw22164step3Labels = raw22164step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22164step3 raw22164step3Labels = mixedMoment B raw22164step4 raw22164step4Labels := by
      have ha : raw22164step4 = raw22164step3 := by apply Matrix.ext; unfold raw22164step4 raw22164step3; decide +kernel
      have hl : raw22164step3Labels = labelEmbedding1 ∘ raw22164step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22164step3 raw22164step3Labels raw22164step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1080 node1080Labels := by rfl

def raw22165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22165step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22165step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22165step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22165step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22165 raw22165Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw22165 raw22165Labels = mixedMoment B raw22165step0 raw22165step0Labels := by
      have hz : ∀ j, raw22165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22165step0 = (fun i j => raw22165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22165step0 raw22165; decide +kernel
      have hl : raw22165step0Labels = raw22165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22165 raw22165Labels permutation434 hz
    mixedMoment B raw22165step0 raw22165step0Labels = mixedMoment B raw22165step1 raw22165step1Labels := by
      have hz : ∀ j, raw22165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22165step1 = (fun i j => raw22165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22165step1 raw22165step0; decide +kernel
      have hl : raw22165step1Labels = raw22165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22165step0 raw22165step0Labels permutation80 hz
    mixedMoment B raw22165step1 raw22165step1Labels = mixedMoment B raw22165step2 raw22165step2Labels := by
      have ha : raw22165step2 = (fun i j => raw22165step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22165step2 raw22165step1; decide +kernel
      have hl : raw22165step2Labels = raw22165step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22165step1 raw22165step1Labels permutation8 permutation7
    mixedMoment B raw22165step2 raw22165step2Labels = mixedMoment B raw22165step3 raw22165step3Labels := by
      have ha : raw22165step3 = -raw22165step2 := by apply Matrix.ext; change ∀ i j, raw22165step3 i j = -(raw22165step2 i j); unfold raw22165step3 raw22165step2; decide +kernel
      have hl : raw22165step3Labels = raw22165step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22165step3 raw22165step3Labels = mixedMoment B raw22165step4 raw22165step4Labels := by
      have ha : raw22165step4 = raw22165step3 := by apply Matrix.ext; unfold raw22165step4 raw22165step3; decide +kernel
      have hl : raw22165step3Labels = labelEmbedding1 ∘ raw22165step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22165step3 raw22165step3Labels raw22165step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1082 node1082Labels := by rfl

def raw22166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22166step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22166step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22166step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22166step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22166step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22166step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22166step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22166 raw22166Labels = mixedMoment B node688 node688Labels := by
  calc
    mixedMoment B raw22166 raw22166Labels = mixedMoment B raw22166step0 raw22166step0Labels := by
      have hz : ∀ j, raw22166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22166step0 = (fun i j => raw22166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22166step0 raw22166; decide +kernel
      have hl : raw22166step0Labels = raw22166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22166 raw22166Labels permutation434 hz
    mixedMoment B raw22166step0 raw22166step0Labels = mixedMoment B raw22166step1 raw22166step1Labels := by
      have hz : ∀ j, raw22166step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22166step1 = (fun i j => raw22166step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22166step1 raw22166step0; decide +kernel
      have hl : raw22166step1Labels = raw22166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22166step0 raw22166step0Labels permutation80 hz
    mixedMoment B raw22166step1 raw22166step1Labels = mixedMoment B raw22166step2 raw22166step2Labels := by
      have ha : raw22166step2 = (fun i j => raw22166step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22166step2 raw22166step1; decide +kernel
      have hl : raw22166step2Labels = raw22166step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22166step1 raw22166step1Labels permutation8 permutation7
    mixedMoment B raw22166step2 raw22166step2Labels = mixedMoment B raw22166step3 raw22166step3Labels := by
      have ha : raw22166step3 = -raw22166step2 := by apply Matrix.ext; change ∀ i j, raw22166step3 i j = -(raw22166step2 i j); unfold raw22166step3 raw22166step2; decide +kernel
      have hl : raw22166step3Labels = raw22166step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22166step3 raw22166step3Labels = mixedMoment B raw22166step4 raw22166step4Labels := by
      have ha : raw22166step4 = raw22166step3 := by apply Matrix.ext; unfold raw22166step4 raw22166step3; decide +kernel
      have hl : raw22166step3Labels = labelEmbedding1 ∘ raw22166step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22166step3 raw22166step3Labels raw22166step4Labels labelEmbedding1 hl
    _ = mixedMoment B node688 node688Labels := by rfl

def raw22167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22167step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22167step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22167step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22167step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22167 raw22167Labels = mixedMoment B node767 node767Labels := by
  calc
    mixedMoment B raw22167 raw22167Labels = mixedMoment B raw22167step0 raw22167step0Labels := by
      have hz : ∀ j, raw22167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22167step0 = (fun i j => raw22167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22167step0 raw22167; decide +kernel
      have hl : raw22167step0Labels = raw22167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22167 raw22167Labels permutation434 hz
    mixedMoment B raw22167step0 raw22167step0Labels = mixedMoment B raw22167step1 raw22167step1Labels := by
      have ha : raw22167step1 = (fun i j => raw22167step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22167step1 raw22167step0; decide +kernel
      have hl : raw22167step1Labels = raw22167step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22167step0 raw22167step0Labels permutation38 permutation7
    mixedMoment B raw22167step1 raw22167step1Labels = mixedMoment B raw22167step2 raw22167step2Labels := by
      have ha : raw22167step2 = -raw22167step1 := by apply Matrix.ext; change ∀ i j, raw22167step2 i j = -(raw22167step1 i j); unfold raw22167step2 raw22167step1; decide +kernel
      have hl : raw22167step2Labels = raw22167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22167step2 raw22167step2Labels = mixedMoment B raw22167step3 raw22167step3Labels := by
      have ha : raw22167step3 = raw22167step2 := by apply Matrix.ext; unfold raw22167step3 raw22167step2; decide +kernel
      have hl : raw22167step2Labels = labelEmbedding1 ∘ raw22167step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22167step2 raw22167step2Labels raw22167step3Labels labelEmbedding1 hl
    _ = mixedMoment B node767 node767Labels := by rfl

def raw22168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22168step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22168step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22168step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22168step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22168 raw22168Labels = mixedMoment B node767 node767Labels := by
  calc
    mixedMoment B raw22168 raw22168Labels = mixedMoment B raw22168step0 raw22168step0Labels := by
      have hz : ∀ j, raw22168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22168step0 = (fun i j => raw22168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22168step0 raw22168; decide +kernel
      have hl : raw22168step0Labels = raw22168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22168 raw22168Labels permutation346 hz
    mixedMoment B raw22168step0 raw22168step0Labels = mixedMoment B raw22168step1 raw22168step1Labels := by
      have ha : raw22168step1 = (fun i j => raw22168step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22168step1 raw22168step0; decide +kernel
      have hl : raw22168step1Labels = raw22168step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22168step0 raw22168step0Labels permutation38 permutation7
    mixedMoment B raw22168step1 raw22168step1Labels = mixedMoment B raw22168step2 raw22168step2Labels := by
      have ha : raw22168step2 = -raw22168step1 := by apply Matrix.ext; change ∀ i j, raw22168step2 i j = -(raw22168step1 i j); unfold raw22168step2 raw22168step1; decide +kernel
      have hl : raw22168step2Labels = raw22168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22168step2 raw22168step2Labels = mixedMoment B raw22168step3 raw22168step3Labels := by
      have ha : raw22168step3 = raw22168step2 := by apply Matrix.ext; unfold raw22168step3 raw22168step2; decide +kernel
      have hl : raw22168step2Labels = labelEmbedding1 ∘ raw22168step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22168step2 raw22168step2Labels raw22168step3Labels labelEmbedding1 hl
    _ = mixedMoment B node767 node767Labels := by rfl

def raw22169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22169step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22169step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22169step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22169step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22169step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22169step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22169step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22169 raw22169Labels = mixedMoment B node851 node851Labels := by
  calc
    mixedMoment B raw22169 raw22169Labels = mixedMoment B raw22169step0 raw22169step0Labels := by
      have hz : ∀ j, raw22169 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22169step0 = (fun i j => raw22169 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22169step0 raw22169; decide +kernel
      have hl : raw22169step0Labels = raw22169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22169 raw22169Labels permutation434 hz
    mixedMoment B raw22169step0 raw22169step0Labels = mixedMoment B raw22169step1 raw22169step1Labels := by
      have hz : ∀ j, raw22169step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22169step1 = (fun i j => raw22169step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22169step1 raw22169step0; decide +kernel
      have hl : raw22169step1Labels = raw22169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22169step0 raw22169step0Labels permutation80 hz
    mixedMoment B raw22169step1 raw22169step1Labels = mixedMoment B raw22169step2 raw22169step2Labels := by
      have ha : raw22169step2 = (fun i j => raw22169step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22169step2 raw22169step1; decide +kernel
      have hl : raw22169step2Labels = raw22169step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22169step1 raw22169step1Labels permutation10 permutation7
    mixedMoment B raw22169step2 raw22169step2Labels = mixedMoment B raw22169step3 raw22169step3Labels := by
      have ha : raw22169step3 = -raw22169step2 := by apply Matrix.ext; change ∀ i j, raw22169step3 i j = -(raw22169step2 i j); unfold raw22169step3 raw22169step2; decide +kernel
      have hl : raw22169step3Labels = raw22169step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22169step3 raw22169step3Labels = mixedMoment B raw22169step4 raw22169step4Labels := by
      have ha : raw22169step4 = raw22169step3 := by apply Matrix.ext; unfold raw22169step4 raw22169step3; decide +kernel
      have hl : raw22169step3Labels = labelEmbedding1 ∘ raw22169step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22169step3 raw22169step3Labels raw22169step4Labels labelEmbedding1 hl
    _ = mixedMoment B node851 node851Labels := by rfl

def raw22170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22170step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22170step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22170step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22170 raw22170Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22170 raw22170Labels = mixedMoment B raw22170step0 raw22170step0Labels := by
      have hz : ∀ j, raw22170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22170step0 = (fun i j => raw22170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22170step0 raw22170; decide +kernel
      have hl : raw22170step0Labels = raw22170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22170 raw22170Labels permutation434 hz
    mixedMoment B raw22170step0 raw22170step0Labels = mixedMoment B raw22170step1 raw22170step1Labels := by
      have hz : ∀ j, raw22170step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22170step1 = (fun i j => raw22170step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22170step1 raw22170step0; decide +kernel
      have hl : raw22170step1Labels = raw22170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22170step0 raw22170step0Labels permutation80 hz
    mixedMoment B raw22170step1 raw22170step1Labels = mixedMoment B raw22170step2 raw22170step2Labels := by
      have hz : ∀ i, raw22170step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw22170step2 = (fun i j => raw22170step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw22170step2 raw22170step1; decide +kernel
      have hl : raw22170step2Labels = (fun j => raw22170step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22170step1 raw22170step1Labels permutation4 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw22171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22171step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22171step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22171step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22171step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22171 raw22171Labels = mixedMoment B node663 node663Labels := by
  calc
    mixedMoment B raw22171 raw22171Labels = mixedMoment B raw22171step0 raw22171step0Labels := by
      have hz : ∀ j, raw22171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22171step0 = (fun i j => raw22171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22171step0 raw22171; decide +kernel
      have hl : raw22171step0Labels = raw22171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22171 raw22171Labels permutation434 hz
    mixedMoment B raw22171step0 raw22171step0Labels = mixedMoment B raw22171step1 raw22171step1Labels := by
      have ha : raw22171step1 = (fun i j => raw22171step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22171step1 raw22171step0; decide +kernel
      have hl : raw22171step1Labels = raw22171step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22171step0 raw22171step0Labels permutation38 permutation7
    mixedMoment B raw22171step1 raw22171step1Labels = mixedMoment B raw22171step2 raw22171step2Labels := by
      have ha : raw22171step2 = -raw22171step1 := by apply Matrix.ext; change ∀ i j, raw22171step2 i j = -(raw22171step1 i j); unfold raw22171step2 raw22171step1; decide +kernel
      have hl : raw22171step2Labels = raw22171step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22171step2 raw22171step2Labels = mixedMoment B raw22171step3 raw22171step3Labels := by
      have ha : raw22171step3 = raw22171step2 := by apply Matrix.ext; unfold raw22171step3 raw22171step2; decide +kernel
      have hl : raw22171step2Labels = labelEmbedding1 ∘ raw22171step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22171step2 raw22171step2Labels raw22171step3Labels labelEmbedding1 hl
    _ = mixedMoment B node663 node663Labels := by rfl

def raw22172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22172step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22172step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22172 raw22172Labels = mixedMoment B node799 node799Labels := by
  calc
    mixedMoment B raw22172 raw22172Labels = mixedMoment B raw22172step0 raw22172step0Labels := by
      have hz : ∀ j, raw22172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22172step0 = (fun i j => raw22172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22172step0 raw22172; decide +kernel
      have hl : raw22172step0Labels = raw22172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22172 raw22172Labels permutation434 hz
    mixedMoment B raw22172step0 raw22172step0Labels = mixedMoment B raw22172step1 raw22172step1Labels := by
      have ha : raw22172step1 = (fun i j => raw22172step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22172step1 raw22172step0; decide +kernel
      have hl : raw22172step1Labels = raw22172step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22172step0 raw22172step0Labels permutation38 permutation7
    mixedMoment B raw22172step1 raw22172step1Labels = mixedMoment B raw22172step2 raw22172step2Labels := by
      have ha : raw22172step2 = -raw22172step1 := by apply Matrix.ext; change ∀ i j, raw22172step2 i j = -(raw22172step1 i j); unfold raw22172step2 raw22172step1; decide +kernel
      have hl : raw22172step2Labels = raw22172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22172step2 raw22172step2Labels = mixedMoment B raw22172step3 raw22172step3Labels := by
      have ha : raw22172step3 = raw22172step2 := by apply Matrix.ext; unfold raw22172step3 raw22172step2; decide +kernel
      have hl : raw22172step2Labels = labelEmbedding1 ∘ raw22172step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22172step2 raw22172step2Labels raw22172step3Labels labelEmbedding1 hl
    _ = mixedMoment B node799 node799Labels := by rfl

def raw22173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22173step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22173 raw22173Labels = mixedMoment B node748 node748Labels := by
  calc
    mixedMoment B raw22173 raw22173Labels = mixedMoment B raw22173step0 raw22173step0Labels := by
      have ha : raw22173step0 = (fun i j => raw22173 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22173step0 raw22173; decide +kernel
      have hl : raw22173step0Labels = raw22173Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22173 raw22173Labels permutation206 permutation7
    mixedMoment B raw22173step0 raw22173step0Labels = mixedMoment B raw22173step1 raw22173step1Labels := by
      have ha : raw22173step1 = -raw22173step0 := by apply Matrix.ext; change ∀ i j, raw22173step1 i j = -(raw22173step0 i j); unfold raw22173step1 raw22173step0; decide +kernel
      have hl : raw22173step1Labels = raw22173step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22173step1 raw22173step1Labels = mixedMoment B raw22173step2 raw22173step2Labels := by
      have ha : raw22173step2 = raw22173step1 := by apply Matrix.ext; unfold raw22173step2 raw22173step1; decide +kernel
      have hl : raw22173step1Labels = labelEmbedding1 ∘ raw22173step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22173step1 raw22173step1Labels raw22173step2Labels labelEmbedding1 hl
    _ = mixedMoment B node748 node748Labels := by rfl

def raw22174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22174step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22174step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22174 raw22174Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw22174 raw22174Labels = mixedMoment B raw22174step0 raw22174step0Labels := by
      have hz : ∀ j, raw22174 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22174step0 = (fun i j => raw22174 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22174step0 raw22174; decide +kernel
      have hl : raw22174step0Labels = raw22174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22174 raw22174Labels permutation434 hz
    mixedMoment B raw22174step0 raw22174step0Labels = mixedMoment B raw22174step1 raw22174step1Labels := by
      have ha : raw22174step1 = (fun i j => raw22174step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22174step1 raw22174step0; decide +kernel
      have hl : raw22174step1Labels = raw22174step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22174step0 raw22174step0Labels permutation38 permutation7
    mixedMoment B raw22174step1 raw22174step1Labels = mixedMoment B raw22174step2 raw22174step2Labels := by
      have ha : raw22174step2 = -raw22174step1 := by apply Matrix.ext; change ∀ i j, raw22174step2 i j = -(raw22174step1 i j); unfold raw22174step2 raw22174step1; decide +kernel
      have hl : raw22174step2Labels = raw22174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22174step2 raw22174step2Labels = mixedMoment B raw22174step3 raw22174step3Labels := by
      have ha : raw22174step3 = raw22174step2 := by apply Matrix.ext; unfold raw22174step3 raw22174step2; decide +kernel
      have hl : raw22174step2Labels = labelEmbedding1 ∘ raw22174step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22174step2 raw22174step2Labels raw22174step3Labels labelEmbedding1 hl
    _ = mixedMoment B node804 node804Labels := by rfl

def raw22175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22175step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22175 raw22175Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw22175 raw22175Labels = mixedMoment B raw22175step0 raw22175step0Labels := by
      have hz : ∀ j, raw22175 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22175step0 = (fun i j => raw22175 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22175step0 raw22175; decide +kernel
      have hl : raw22175step0Labels = raw22175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22175 raw22175Labels permutation434 hz
    mixedMoment B raw22175step0 raw22175step0Labels = mixedMoment B raw22175step1 raw22175step1Labels := by
      have ha : raw22175step1 = (fun i j => raw22175step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22175step1 raw22175step0; decide +kernel
      have hl : raw22175step1Labels = raw22175step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22175step0 raw22175step0Labels permutation38 permutation7
    mixedMoment B raw22175step1 raw22175step1Labels = mixedMoment B raw22175step2 raw22175step2Labels := by
      have ha : raw22175step2 = -raw22175step1 := by apply Matrix.ext; change ∀ i j, raw22175step2 i j = -(raw22175step1 i j); unfold raw22175step2 raw22175step1; decide +kernel
      have hl : raw22175step2Labels = raw22175step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22175step2 raw22175step2Labels = mixedMoment B raw22175step3 raw22175step3Labels := by
      have ha : raw22175step3 = raw22175step2 := by apply Matrix.ext; unfold raw22175step3 raw22175step2; decide +kernel
      have hl : raw22175step2Labels = labelEmbedding1 ∘ raw22175step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22175step2 raw22175step2Labels raw22175step3Labels labelEmbedding1 hl
    _ = mixedMoment B node806 node806Labels := by rfl

def raw22176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22176 raw22176Labels = mixedMoment B node663 node663Labels := by
  calc
    mixedMoment B raw22176 raw22176Labels = mixedMoment B raw22176step0 raw22176step0Labels := by
      have hz : ∀ j, raw22176 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22176step0 = (fun i j => raw22176 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22176step0 raw22176; decide +kernel
      have hl : raw22176step0Labels = raw22176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22176 raw22176Labels permutation346 hz
    mixedMoment B raw22176step0 raw22176step0Labels = mixedMoment B raw22176step1 raw22176step1Labels := by
      have ha : raw22176step1 = (fun i j => raw22176step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22176step1 raw22176step0; decide +kernel
      have hl : raw22176step1Labels = raw22176step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22176step0 raw22176step0Labels permutation38 permutation7
    mixedMoment B raw22176step1 raw22176step1Labels = mixedMoment B raw22176step2 raw22176step2Labels := by
      have ha : raw22176step2 = -raw22176step1 := by apply Matrix.ext; change ∀ i j, raw22176step2 i j = -(raw22176step1 i j); unfold raw22176step2 raw22176step1; decide +kernel
      have hl : raw22176step2Labels = raw22176step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22176step2 raw22176step2Labels = mixedMoment B raw22176step3 raw22176step3Labels := by
      have ha : raw22176step3 = raw22176step2 := by apply Matrix.ext; unfold raw22176step3 raw22176step2; decide +kernel
      have hl : raw22176step2Labels = labelEmbedding1 ∘ raw22176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22176step2 raw22176step2Labels raw22176step3Labels labelEmbedding1 hl
    _ = mixedMoment B node663 node663Labels := by rfl

def raw22177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22177step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22177step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22177step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22177 raw22177Labels = mixedMoment B node799 node799Labels := by
  calc
    mixedMoment B raw22177 raw22177Labels = mixedMoment B raw22177step0 raw22177step0Labels := by
      have hz : ∀ j, raw22177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22177step0 = (fun i j => raw22177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22177step0 raw22177; decide +kernel
      have hl : raw22177step0Labels = raw22177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22177 raw22177Labels permutation346 hz
    mixedMoment B raw22177step0 raw22177step0Labels = mixedMoment B raw22177step1 raw22177step1Labels := by
      have ha : raw22177step1 = (fun i j => raw22177step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22177step1 raw22177step0; decide +kernel
      have hl : raw22177step1Labels = raw22177step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22177step0 raw22177step0Labels permutation38 permutation7
    mixedMoment B raw22177step1 raw22177step1Labels = mixedMoment B raw22177step2 raw22177step2Labels := by
      have ha : raw22177step2 = -raw22177step1 := by apply Matrix.ext; change ∀ i j, raw22177step2 i j = -(raw22177step1 i j); unfold raw22177step2 raw22177step1; decide +kernel
      have hl : raw22177step2Labels = raw22177step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22177step2 raw22177step2Labels = mixedMoment B raw22177step3 raw22177step3Labels := by
      have ha : raw22177step3 = raw22177step2 := by apply Matrix.ext; unfold raw22177step3 raw22177step2; decide +kernel
      have hl : raw22177step2Labels = labelEmbedding1 ∘ raw22177step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22177step2 raw22177step2Labels raw22177step3Labels labelEmbedding1 hl
    _ = mixedMoment B node799 node799Labels := by rfl

def raw22178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22178step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22178 raw22178Labels = mixedMoment B node748 node748Labels := by
  calc
    mixedMoment B raw22178 raw22178Labels = mixedMoment B raw22178step0 raw22178step0Labels := by
      have ha : raw22178step0 = (fun i j => raw22178 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22178step0 raw22178; decide +kernel
      have hl : raw22178step0Labels = raw22178Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22178 raw22178Labels permutation182 permutation7
    mixedMoment B raw22178step0 raw22178step0Labels = mixedMoment B raw22178step1 raw22178step1Labels := by
      have ha : raw22178step1 = -raw22178step0 := by apply Matrix.ext; change ∀ i j, raw22178step1 i j = -(raw22178step0 i j); unfold raw22178step1 raw22178step0; decide +kernel
      have hl : raw22178step1Labels = raw22178step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22178step1 raw22178step1Labels = mixedMoment B raw22178step2 raw22178step2Labels := by
      have ha : raw22178step2 = raw22178step1 := by apply Matrix.ext; unfold raw22178step2 raw22178step1; decide +kernel
      have hl : raw22178step1Labels = labelEmbedding1 ∘ raw22178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22178step1 raw22178step1Labels raw22178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node748 node748Labels := by rfl

def raw22179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22179step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22179step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22179 raw22179Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw22179 raw22179Labels = mixedMoment B raw22179step0 raw22179step0Labels := by
      have hz : ∀ j, raw22179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22179step0 = (fun i j => raw22179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22179step0 raw22179; decide +kernel
      have hl : raw22179step0Labels = raw22179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22179 raw22179Labels permutation346 hz
    mixedMoment B raw22179step0 raw22179step0Labels = mixedMoment B raw22179step1 raw22179step1Labels := by
      have ha : raw22179step1 = (fun i j => raw22179step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22179step1 raw22179step0; decide +kernel
      have hl : raw22179step1Labels = raw22179step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22179step0 raw22179step0Labels permutation38 permutation7
    mixedMoment B raw22179step1 raw22179step1Labels = mixedMoment B raw22179step2 raw22179step2Labels := by
      have ha : raw22179step2 = -raw22179step1 := by apply Matrix.ext; change ∀ i j, raw22179step2 i j = -(raw22179step1 i j); unfold raw22179step2 raw22179step1; decide +kernel
      have hl : raw22179step2Labels = raw22179step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22179step2 raw22179step2Labels = mixedMoment B raw22179step3 raw22179step3Labels := by
      have ha : raw22179step3 = raw22179step2 := by apply Matrix.ext; unfold raw22179step3 raw22179step2; decide +kernel
      have hl : raw22179step2Labels = labelEmbedding1 ∘ raw22179step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22179step2 raw22179step2Labels raw22179step3Labels labelEmbedding1 hl
    _ = mixedMoment B node804 node804Labels := by rfl

def raw22180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22180 raw22180Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw22180 raw22180Labels = mixedMoment B raw22180step0 raw22180step0Labels := by
      have hz : ∀ j, raw22180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22180step0 = (fun i j => raw22180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22180step0 raw22180; decide +kernel
      have hl : raw22180step0Labels = raw22180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22180 raw22180Labels permutation346 hz
    mixedMoment B raw22180step0 raw22180step0Labels = mixedMoment B raw22180step1 raw22180step1Labels := by
      have ha : raw22180step1 = (fun i j => raw22180step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22180step1 raw22180step0; decide +kernel
      have hl : raw22180step1Labels = raw22180step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22180step0 raw22180step0Labels permutation38 permutation7
    mixedMoment B raw22180step1 raw22180step1Labels = mixedMoment B raw22180step2 raw22180step2Labels := by
      have ha : raw22180step2 = -raw22180step1 := by apply Matrix.ext; change ∀ i j, raw22180step2 i j = -(raw22180step1 i j); unfold raw22180step2 raw22180step1; decide +kernel
      have hl : raw22180step2Labels = raw22180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22180step2 raw22180step2Labels = mixedMoment B raw22180step3 raw22180step3Labels := by
      have ha : raw22180step3 = raw22180step2 := by apply Matrix.ext; unfold raw22180step3 raw22180step2; decide +kernel
      have hl : raw22180step2Labels = labelEmbedding1 ∘ raw22180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22180step2 raw22180step2Labels raw22180step3Labels labelEmbedding1 hl
    _ = mixedMoment B node806 node806Labels := by rfl

def raw22181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22181step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22181step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw22181step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22181step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22181step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22181step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22181 raw22181Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw22181 raw22181Labels = mixedMoment B raw22181step0 raw22181step0Labels := by
      have hz : ∀ j, raw22181 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22181step0 = (fun i j => raw22181 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22181step0 raw22181; decide +kernel
      have hl : raw22181step0Labels = raw22181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22181 raw22181Labels permutation434 hz
    mixedMoment B raw22181step0 raw22181step0Labels = mixedMoment B raw22181step1 raw22181step1Labels := by
      have hz : ∀ j, raw22181step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22181step1 = (fun i j => raw22181step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22181step1 raw22181step0; decide +kernel
      have hl : raw22181step1Labels = raw22181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22181step0 raw22181step0Labels permutation80 hz
    mixedMoment B raw22181step1 raw22181step1Labels = mixedMoment B raw22181step2 raw22181step2Labels := by
      have ha : raw22181step2 = (fun i j => raw22181step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22181step2 raw22181step1; decide +kernel
      have hl : raw22181step2Labels = raw22181step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22181step1 raw22181step1Labels permutation8 permutation7
    mixedMoment B raw22181step2 raw22181step2Labels = mixedMoment B raw22181step3 raw22181step3Labels := by
      have ha : raw22181step3 = -raw22181step2 := by apply Matrix.ext; change ∀ i j, raw22181step3 i j = -(raw22181step2 i j); unfold raw22181step3 raw22181step2; decide +kernel
      have hl : raw22181step3Labels = raw22181step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22181step3 raw22181step3Labels = mixedMoment B raw22181step4 raw22181step4Labels := by
      have ha : raw22181step4 = raw22181step3 := by apply Matrix.ext; unfold raw22181step4 raw22181step3; decide +kernel
      have hl : raw22181step3Labels = labelEmbedding1 ∘ raw22181step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22181step3 raw22181step3Labels raw22181step4Labels labelEmbedding1 hl
    _ = mixedMoment B node684 node684Labels := by rfl

def raw22182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22182step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw22182step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22182step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22182step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22182step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22182step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22182 raw22182Labels = mixedMoment B node843 node843Labels := by
  calc
    mixedMoment B raw22182 raw22182Labels = mixedMoment B raw22182step0 raw22182step0Labels := by
      have hz : ∀ j, raw22182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22182step0 = (fun i j => raw22182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22182step0 raw22182; decide +kernel
      have hl : raw22182step0Labels = raw22182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22182 raw22182Labels permutation434 hz
    mixedMoment B raw22182step0 raw22182step0Labels = mixedMoment B raw22182step1 raw22182step1Labels := by
      have hz : ∀ j, raw22182step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22182step1 = (fun i j => raw22182step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22182step1 raw22182step0; decide +kernel
      have hl : raw22182step1Labels = raw22182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22182step0 raw22182step0Labels permutation80 hz
    mixedMoment B raw22182step1 raw22182step1Labels = mixedMoment B raw22182step2 raw22182step2Labels := by
      have ha : raw22182step2 = (fun i j => raw22182step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22182step2 raw22182step1; decide +kernel
      have hl : raw22182step2Labels = raw22182step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22182step1 raw22182step1Labels permutation8 permutation7
    mixedMoment B raw22182step2 raw22182step2Labels = mixedMoment B raw22182step3 raw22182step3Labels := by
      have ha : raw22182step3 = -raw22182step2 := by apply Matrix.ext; change ∀ i j, raw22182step3 i j = -(raw22182step2 i j); unfold raw22182step3 raw22182step2; decide +kernel
      have hl : raw22182step3Labels = raw22182step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22182step3 raw22182step3Labels = mixedMoment B raw22182step4 raw22182step4Labels := by
      have ha : raw22182step4 = raw22182step3 := by apply Matrix.ext; unfold raw22182step4 raw22182step3; decide +kernel
      have hl : raw22182step3Labels = labelEmbedding1 ∘ raw22182step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22182step3 raw22182step3Labels raw22182step4Labels labelEmbedding1 hl
    _ = mixedMoment B node843 node843Labels := by rfl

def raw22183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22183step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw22183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22183step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22183step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22183step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22183 raw22183Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw22183 raw22183Labels = mixedMoment B raw22183step0 raw22183step0Labels := by
      have hz : ∀ j, raw22183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22183step0 = (fun i j => raw22183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22183step0 raw22183; decide +kernel
      have hl : raw22183step0Labels = raw22183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22183 raw22183Labels permutation434 hz
    mixedMoment B raw22183step0 raw22183step0Labels = mixedMoment B raw22183step1 raw22183step1Labels := by
      have ha : raw22183step1 = (fun i j => raw22183step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22183step1 raw22183step0; decide +kernel
      have hl : raw22183step1Labels = raw22183step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22183step0 raw22183step0Labels permutation38 permutation7
    mixedMoment B raw22183step1 raw22183step1Labels = mixedMoment B raw22183step2 raw22183step2Labels := by
      have ha : raw22183step2 = -raw22183step1 := by apply Matrix.ext; change ∀ i j, raw22183step2 i j = -(raw22183step1 i j); unfold raw22183step2 raw22183step1; decide +kernel
      have hl : raw22183step2Labels = raw22183step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22183step2 raw22183step2Labels = mixedMoment B raw22183step3 raw22183step3Labels := by
      have ha : raw22183step3 = raw22183step2 := by apply Matrix.ext; unfold raw22183step3 raw22183step2; decide +kernel
      have hl : raw22183step2Labels = labelEmbedding1 ∘ raw22183step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22183step2 raw22183step2Labels raw22183step3Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

def raw22184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22184step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw22184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22184step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22184step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22184 raw22184Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw22184 raw22184Labels = mixedMoment B raw22184step0 raw22184step0Labels := by
      have hz : ∀ j, raw22184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22184step0 = (fun i j => raw22184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22184step0 raw22184; decide +kernel
      have hl : raw22184step0Labels = raw22184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22184 raw22184Labels permutation346 hz
    mixedMoment B raw22184step0 raw22184step0Labels = mixedMoment B raw22184step1 raw22184step1Labels := by
      have ha : raw22184step1 = (fun i j => raw22184step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22184step1 raw22184step0; decide +kernel
      have hl : raw22184step1Labels = raw22184step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22184step0 raw22184step0Labels permutation38 permutation7
    mixedMoment B raw22184step1 raw22184step1Labels = mixedMoment B raw22184step2 raw22184step2Labels := by
      have ha : raw22184step2 = -raw22184step1 := by apply Matrix.ext; change ∀ i j, raw22184step2 i j = -(raw22184step1 i j); unfold raw22184step2 raw22184step1; decide +kernel
      have hl : raw22184step2Labels = raw22184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22184step2 raw22184step2Labels = mixedMoment B raw22184step3 raw22184step3Labels := by
      have ha : raw22184step3 = raw22184step2 := by apply Matrix.ext; unfold raw22184step3 raw22184step2; decide +kernel
      have hl : raw22184step2Labels = labelEmbedding1 ∘ raw22184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22184step2 raw22184step2Labels raw22184step3Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

def raw22185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22185step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22185step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22185step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22185step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22185step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22185 raw22185Labels = mixedMoment B node852 node852Labels := by
  calc
    mixedMoment B raw22185 raw22185Labels = mixedMoment B raw22185step0 raw22185step0Labels := by
      have hz : ∀ j, raw22185 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22185step0 = (fun i j => raw22185 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22185step0 raw22185; decide +kernel
      have hl : raw22185step0Labels = raw22185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22185 raw22185Labels permutation434 hz
    mixedMoment B raw22185step0 raw22185step0Labels = mixedMoment B raw22185step1 raw22185step1Labels := by
      have hz : ∀ j, raw22185step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22185step1 = (fun i j => raw22185step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22185step1 raw22185step0; decide +kernel
      have hl : raw22185step1Labels = raw22185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22185step0 raw22185step0Labels permutation80 hz
    mixedMoment B raw22185step1 raw22185step1Labels = mixedMoment B raw22185step2 raw22185step2Labels := by
      have ha : raw22185step2 = (fun i j => raw22185step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22185step2 raw22185step1; decide +kernel
      have hl : raw22185step2Labels = raw22185step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22185step1 raw22185step1Labels permutation8 permutation7
    mixedMoment B raw22185step2 raw22185step2Labels = mixedMoment B raw22185step3 raw22185step3Labels := by
      have ha : raw22185step3 = -raw22185step2 := by apply Matrix.ext; change ∀ i j, raw22185step3 i j = -(raw22185step2 i j); unfold raw22185step3 raw22185step2; decide +kernel
      have hl : raw22185step3Labels = raw22185step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22185step3 raw22185step3Labels = mixedMoment B raw22185step4 raw22185step4Labels := by
      have ha : raw22185step4 = raw22185step3 := by apply Matrix.ext; unfold raw22185step4 raw22185step3; decide +kernel
      have hl : raw22185step3Labels = labelEmbedding1 ∘ raw22185step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22185step3 raw22185step3Labels raw22185step4Labels labelEmbedding1 hl
    _ = mixedMoment B node852 node852Labels := by rfl

def raw22186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22186step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw22186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22186step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22186step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22186step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22186 raw22186Labels = mixedMoment B node683 node683Labels := by
  calc
    mixedMoment B raw22186 raw22186Labels = mixedMoment B raw22186step0 raw22186step0Labels := by
      have hz : ∀ j, raw22186 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22186step0 = (fun i j => raw22186 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22186step0 raw22186; decide +kernel
      have hl : raw22186step0Labels = raw22186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22186 raw22186Labels permutation434 hz
    mixedMoment B raw22186step0 raw22186step0Labels = mixedMoment B raw22186step1 raw22186step1Labels := by
      have hz : ∀ j, raw22186step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22186step1 = (fun i j => raw22186step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22186step1 raw22186step0; decide +kernel
      have hl : raw22186step1Labels = raw22186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22186step0 raw22186step0Labels permutation80 hz
    mixedMoment B raw22186step1 raw22186step1Labels = mixedMoment B raw22186step2 raw22186step2Labels := by
      have ha : raw22186step2 = (fun i j => raw22186step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22186step2 raw22186step1; decide +kernel
      have hl : raw22186step2Labels = raw22186step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22186step1 raw22186step1Labels permutation8 permutation7
    mixedMoment B raw22186step2 raw22186step2Labels = mixedMoment B raw22186step3 raw22186step3Labels := by
      have ha : raw22186step3 = -raw22186step2 := by apply Matrix.ext; change ∀ i j, raw22186step3 i j = -(raw22186step2 i j); unfold raw22186step3 raw22186step2; decide +kernel
      have hl : raw22186step3Labels = raw22186step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22186step3 raw22186step3Labels = mixedMoment B raw22186step4 raw22186step4Labels := by
      have ha : raw22186step4 = raw22186step3 := by apply Matrix.ext; unfold raw22186step4 raw22186step3; decide +kernel
      have hl : raw22186step3Labels = labelEmbedding1 ∘ raw22186step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22186step3 raw22186step3Labels raw22186step4Labels labelEmbedding1 hl
    _ = mixedMoment B node683 node683Labels := by rfl

def raw22187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22187step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22187step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw22187step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22187step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw22187step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22187step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw22187step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22187 raw22187Labels = mixedMoment B node842 node842Labels := by
  calc
    mixedMoment B raw22187 raw22187Labels = mixedMoment B raw22187step0 raw22187step0Labels := by
      have hz : ∀ j, raw22187 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22187step0 = (fun i j => raw22187 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22187step0 raw22187; decide +kernel
      have hl : raw22187step0Labels = raw22187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22187 raw22187Labels permutation434 hz
    mixedMoment B raw22187step0 raw22187step0Labels = mixedMoment B raw22187step1 raw22187step1Labels := by
      have hz : ∀ j, raw22187step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22187step1 = (fun i j => raw22187step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22187step1 raw22187step0; decide +kernel
      have hl : raw22187step1Labels = raw22187step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22187step0 raw22187step0Labels permutation80 hz
    mixedMoment B raw22187step1 raw22187step1Labels = mixedMoment B raw22187step2 raw22187step2Labels := by
      have ha : raw22187step2 = (fun i j => raw22187step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22187step2 raw22187step1; decide +kernel
      have hl : raw22187step2Labels = raw22187step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22187step1 raw22187step1Labels permutation8 permutation7
    mixedMoment B raw22187step2 raw22187step2Labels = mixedMoment B raw22187step3 raw22187step3Labels := by
      have ha : raw22187step3 = -raw22187step2 := by apply Matrix.ext; change ∀ i j, raw22187step3 i j = -(raw22187step2 i j); unfold raw22187step3 raw22187step2; decide +kernel
      have hl : raw22187step3Labels = raw22187step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22187step3 raw22187step3Labels = mixedMoment B raw22187step4 raw22187step4Labels := by
      have ha : raw22187step4 = raw22187step3 := by apply Matrix.ext; unfold raw22187step4 raw22187step3; decide +kernel
      have hl : raw22187step3Labels = labelEmbedding1 ∘ raw22187step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22187step3 raw22187step3Labels raw22187step4Labels labelEmbedding1 hl
    _ = mixedMoment B node842 node842Labels := by rfl

def raw22188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw22188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22188 raw22188Labels = mixedMoment B node762 node762Labels := by
  calc
    mixedMoment B raw22188 raw22188Labels = mixedMoment B raw22188step0 raw22188step0Labels := by
      have hz : ∀ j, raw22188 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22188step0 = (fun i j => raw22188 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22188step0 raw22188; decide +kernel
      have hl : raw22188step0Labels = raw22188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22188 raw22188Labels permutation434 hz
    mixedMoment B raw22188step0 raw22188step0Labels = mixedMoment B raw22188step1 raw22188step1Labels := by
      have ha : raw22188step1 = (fun i j => raw22188step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22188step1 raw22188step0; decide +kernel
      have hl : raw22188step1Labels = raw22188step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22188step0 raw22188step0Labels permutation38 permutation7
    mixedMoment B raw22188step1 raw22188step1Labels = mixedMoment B raw22188step2 raw22188step2Labels := by
      have ha : raw22188step2 = -raw22188step1 := by apply Matrix.ext; change ∀ i j, raw22188step2 i j = -(raw22188step1 i j); unfold raw22188step2 raw22188step1; decide +kernel
      have hl : raw22188step2Labels = raw22188step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22188step2 raw22188step2Labels = mixedMoment B raw22188step3 raw22188step3Labels := by
      have ha : raw22188step3 = raw22188step2 := by apply Matrix.ext; unfold raw22188step3 raw22188step2; decide +kernel
      have hl : raw22188step2Labels = labelEmbedding1 ∘ raw22188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22188step2 raw22188step2Labels raw22188step3Labels labelEmbedding1 hl
    _ = mixedMoment B node762 node762Labels := by rfl

def raw22189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw22189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22189 raw22189Labels = mixedMoment B node762 node762Labels := by
  calc
    mixedMoment B raw22189 raw22189Labels = mixedMoment B raw22189step0 raw22189step0Labels := by
      have hz : ∀ j, raw22189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22189step0 = (fun i j => raw22189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22189step0 raw22189; decide +kernel
      have hl : raw22189step0Labels = raw22189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22189 raw22189Labels permutation346 hz
    mixedMoment B raw22189step0 raw22189step0Labels = mixedMoment B raw22189step1 raw22189step1Labels := by
      have ha : raw22189step1 = (fun i j => raw22189step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22189step1 raw22189step0; decide +kernel
      have hl : raw22189step1Labels = raw22189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22189step0 raw22189step0Labels permutation38 permutation7
    mixedMoment B raw22189step1 raw22189step1Labels = mixedMoment B raw22189step2 raw22189step2Labels := by
      have ha : raw22189step2 = -raw22189step1 := by apply Matrix.ext; change ∀ i j, raw22189step2 i j = -(raw22189step1 i j); unfold raw22189step2 raw22189step1; decide +kernel
      have hl : raw22189step2Labels = raw22189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22189step2 raw22189step2Labels = mixedMoment B raw22189step3 raw22189step3Labels := by
      have ha : raw22189step3 = raw22189step2 := by apply Matrix.ext; unfold raw22189step3 raw22189step2; decide +kernel
      have hl : raw22189step2Labels = labelEmbedding1 ∘ raw22189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22189step2 raw22189step2Labels raw22189step3Labels labelEmbedding1 hl
    _ = mixedMoment B node762 node762Labels := by rfl

def raw22190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw22190step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw22190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22190step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22190step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22190step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22190step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22190 raw22190Labels = mixedMoment B node849 node849Labels := by
  calc
    mixedMoment B raw22190 raw22190Labels = mixedMoment B raw22190step0 raw22190step0Labels := by
      have hz : ∀ j, raw22190 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22190step0 = (fun i j => raw22190 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22190step0 raw22190; decide +kernel
      have hl : raw22190step0Labels = raw22190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22190 raw22190Labels permutation434 hz
    mixedMoment B raw22190step0 raw22190step0Labels = mixedMoment B raw22190step1 raw22190step1Labels := by
      have hz : ∀ j, raw22190step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22190step1 = (fun i j => raw22190step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22190step1 raw22190step0; decide +kernel
      have hl : raw22190step1Labels = raw22190step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22190step0 raw22190step0Labels permutation80 hz
    mixedMoment B raw22190step1 raw22190step1Labels = mixedMoment B raw22190step2 raw22190step2Labels := by
      have ha : raw22190step2 = (fun i j => raw22190step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22190step2 raw22190step1; decide +kernel
      have hl : raw22190step2Labels = raw22190step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22190step1 raw22190step1Labels permutation8 permutation7
    mixedMoment B raw22190step2 raw22190step2Labels = mixedMoment B raw22190step3 raw22190step3Labels := by
      have ha : raw22190step3 = -raw22190step2 := by apply Matrix.ext; change ∀ i j, raw22190step3 i j = -(raw22190step2 i j); unfold raw22190step3 raw22190step2; decide +kernel
      have hl : raw22190step3Labels = raw22190step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22190step3 raw22190step3Labels = mixedMoment B raw22190step4 raw22190step4Labels := by
      have ha : raw22190step4 = raw22190step3 := by apply Matrix.ext; unfold raw22190step4 raw22190step3; decide +kernel
      have hl : raw22190step3Labels = labelEmbedding1 ∘ raw22190step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22190step3 raw22190step3Labels raw22190step4Labels labelEmbedding1 hl
    _ = mixedMoment B node849 node849Labels := by rfl

def raw22191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22191 raw22191Labels = mixedMoment B node812 node812Labels := by
  calc
    mixedMoment B raw22191 raw22191Labels = mixedMoment B raw22191step0 raw22191step0Labels := by
      have hz : ∀ j, raw22191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22191step0 = (fun i j => raw22191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22191step0 raw22191; decide +kernel
      have hl : raw22191step0Labels = raw22191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22191 raw22191Labels permutation434 hz
    mixedMoment B raw22191step0 raw22191step0Labels = mixedMoment B raw22191step1 raw22191step1Labels := by
      have hz : ∀ j, raw22191step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22191step1 = (fun i j => raw22191step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22191step1 raw22191step0; decide +kernel
      have hl : raw22191step1Labels = raw22191step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22191step0 raw22191step0Labels permutation80 hz
    _ = mixedMoment B node812 node812Labels := by rfl

def raw22192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22192step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22192 raw22192Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw22192 raw22192Labels = mixedMoment B raw22192step0 raw22192step0Labels := by
      have hz : ∀ j, raw22192 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22192step0 = (fun i j => raw22192 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22192step0 raw22192; decide +kernel
      have hl : raw22192step0Labels = raw22192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22192 raw22192Labels permutation434 hz
    mixedMoment B raw22192step0 raw22192step0Labels = mixedMoment B raw22192step1 raw22192step1Labels := by
      have hz : ∀ j, raw22192step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22192step1 = (fun i j => raw22192step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22192step1 raw22192step0; decide +kernel
      have hl : raw22192step1Labels = raw22192step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22192step0 raw22192step0Labels permutation80 hz
    _ = mixedMoment B node1650 node1650Labels := by rfl

def raw22193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22193 raw22193Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw22193 raw22193Labels = mixedMoment B raw22193step0 raw22193step0Labels := by
      have hz : ∀ j, raw22193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22193step0 = (fun i j => raw22193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22193step0 raw22193; decide +kernel
      have hl : raw22193step0Labels = raw22193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22193 raw22193Labels permutation434 hz
    mixedMoment B raw22193step0 raw22193step0Labels = mixedMoment B raw22193step1 raw22193step1Labels := by
      have ha : raw22193step1 = (fun i j => raw22193step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22193step1 raw22193step0; decide +kernel
      have hl : raw22193step1Labels = raw22193step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22193step0 raw22193step0Labels permutation38 permutation2
    _ = mixedMoment B node1602 node1602Labels := by rfl

def raw22194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22194 raw22194Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw22194 raw22194Labels = mixedMoment B raw22194step0 raw22194step0Labels := by
      have hz : ∀ j, raw22194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22194step0 = (fun i j => raw22194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22194step0 raw22194; decide +kernel
      have hl : raw22194step0Labels = raw22194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22194 raw22194Labels permutation346 hz
    mixedMoment B raw22194step0 raw22194step0Labels = mixedMoment B raw22194step1 raw22194step1Labels := by
      have ha : raw22194step1 = (fun i j => raw22194step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22194step1 raw22194step0; decide +kernel
      have hl : raw22194step1Labels = raw22194step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22194step0 raw22194step0Labels permutation38 permutation2
    _ = mixedMoment B node1602 node1602Labels := by rfl

def raw22195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22195 raw22195Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw22195 raw22195Labels = mixedMoment B raw22195step0 raw22195step0Labels := by
      have hz : ∀ j, raw22195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22195step0 = (fun i j => raw22195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22195step0 raw22195; decide +kernel
      have hl : raw22195step0Labels = raw22195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22195 raw22195Labels permutation434 hz
    mixedMoment B raw22195step0 raw22195step0Labels = mixedMoment B raw22195step1 raw22195step1Labels := by
      have hz : ∀ j, raw22195step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22195step1 = (fun i j => raw22195step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22195step1 raw22195step0; decide +kernel
      have hl : raw22195step1Labels = raw22195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22195step0 raw22195step0Labels permutation80 hz
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw22196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22196 raw22196Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw22196 raw22196Labels = mixedMoment B raw22196step0 raw22196step0Labels := by
      have hz : ∀ j, raw22196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22196step0 = (fun i j => raw22196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22196step0 raw22196; decide +kernel
      have hl : raw22196step0Labels = raw22196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22196 raw22196Labels permutation434 hz
    mixedMoment B raw22196step0 raw22196step0Labels = mixedMoment B raw22196step1 raw22196step1Labels := by
      have hz : ∀ j, raw22196step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22196step1 = (fun i j => raw22196step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22196step1 raw22196step0; decide +kernel
      have hl : raw22196step1Labels = raw22196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22196step0 raw22196step0Labels permutation80 hz
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw22197 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw22197Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22197step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]
def raw22197step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22197step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22197step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22197 raw22197Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22197 raw22197Labels = mixedMoment B raw22197step0 raw22197step0Labels := by
      have hz : ∀ j, raw22197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22197step0 = (fun i j => raw22197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22197step0 raw22197; decide +kernel
      have hl : raw22197step0Labels = raw22197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22197 raw22197Labels permutation434 hz
    mixedMoment B raw22197step0 raw22197step0Labels = mixedMoment B raw22197step1 raw22197step1Labels := by
      have hz : ∀ j, raw22197step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22197step1 = (fun i j => raw22197step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22197step1 raw22197step0; decide +kernel
      have hl : raw22197step1Labels = raw22197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22197step0 raw22197step0Labels permutation80 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw22198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22198 raw22198Labels = mixedMoment B node558 node558Labels := by
  calc
    mixedMoment B raw22198 raw22198Labels = mixedMoment B raw22198step0 raw22198step0Labels := by
      have hz : ∀ j, raw22198 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22198step0 = (fun i j => raw22198 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22198step0 raw22198; decide +kernel
      have hl : raw22198step0Labels = raw22198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22198 raw22198Labels permutation434 hz
    mixedMoment B raw22198step0 raw22198step0Labels = mixedMoment B raw22198step1 raw22198step1Labels := by
      have hz : ∀ j, raw22198step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22198step1 = (fun i j => raw22198step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22198step1 raw22198step0; decide +kernel
      have hl : raw22198step1Labels = raw22198step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22198step0 raw22198step0Labels permutation80 hz
    _ = mixedMoment B node558 node558Labels := by rfl

def raw22199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22199 raw22199Labels = mixedMoment B node538 node538Labels := by
  calc
    mixedMoment B raw22199 raw22199Labels = mixedMoment B raw22199step0 raw22199step0Labels := by
      have hz : ∀ j, raw22199 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22199step0 = (fun i j => raw22199 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22199step0 raw22199; decide +kernel
      have hl : raw22199step0Labels = raw22199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22199 raw22199Labels permutation434 hz
    _ = mixedMoment B node538 node538Labels := by rfl

def raw22200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22200 raw22200Labels = mixedMoment B node538 node538Labels := by
  calc
    mixedMoment B raw22200 raw22200Labels = mixedMoment B raw22200step0 raw22200step0Labels := by
      have hz : ∀ j, raw22200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22200step0 = (fun i j => raw22200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22200step0 raw22200; decide +kernel
      have hl : raw22200step0Labels = raw22200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22200 raw22200Labels permutation346 hz
    _ = mixedMoment B node538 node538Labels := by rfl

def raw22201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22201 raw22201Labels = mixedMoment B node547 node547Labels := by
  calc
    mixedMoment B raw22201 raw22201Labels = mixedMoment B raw22201step0 raw22201step0Labels := by
      have hz : ∀ j, raw22201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22201step0 = (fun i j => raw22201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22201step0 raw22201; decide +kernel
      have hl : raw22201step0Labels = raw22201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22201 raw22201Labels permutation434 hz
    mixedMoment B raw22201step0 raw22201step0Labels = mixedMoment B raw22201step1 raw22201step1Labels := by
      have hz : ∀ j, raw22201step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22201step1 = (fun i j => raw22201step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22201step1 raw22201step0; decide +kernel
      have hl : raw22201step1Labels = raw22201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22201step0 raw22201step0Labels permutation80 hz
    _ = mixedMoment B node547 node547Labels := by rfl

def raw22202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22202 raw22202Labels = mixedMoment B node545 node545Labels := by
  calc
    mixedMoment B raw22202 raw22202Labels = mixedMoment B raw22202step0 raw22202step0Labels := by
      have hz : ∀ j, raw22202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22202step0 = (fun i j => raw22202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22202step0 raw22202; decide +kernel
      have hl : raw22202step0Labels = raw22202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22202 raw22202Labels permutation434 hz
    mixedMoment B raw22202step0 raw22202step0Labels = mixedMoment B raw22202step1 raw22202step1Labels := by
      have hz : ∀ j, raw22202step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22202step1 = (fun i j => raw22202step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22202step1 raw22202step0; decide +kernel
      have hl : raw22202step1Labels = raw22202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22202step0 raw22202step0Labels permutation80 hz
    _ = mixedMoment B node545 node545Labels := by rfl

def raw22203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22203 raw22203Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw22203 raw22203Labels = mixedMoment B raw22203step0 raw22203step0Labels := by
      have hz : ∀ j, raw22203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22203step0 = (fun i j => raw22203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22203step0 raw22203; decide +kernel
      have hl : raw22203step0Labels = raw22203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22203 raw22203Labels permutation434 hz
    _ = mixedMoment B node733 node733Labels := by rfl

def raw22204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22204 raw22204Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw22204 raw22204Labels = mixedMoment B raw22204step0 raw22204step0Labels := by
      have hz : ∀ j, raw22204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22204step0 = (fun i j => raw22204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22204step0 raw22204; decide +kernel
      have hl : raw22204step0Labels = raw22204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22204 raw22204Labels permutation346 hz
    _ = mixedMoment B node733 node733Labels := by rfl

def raw22205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22205 raw22205Labels = mixedMoment B node742 node742Labels := by
  calc
    mixedMoment B raw22205 raw22205Labels = mixedMoment B raw22205step0 raw22205step0Labels := by
      have hz : ∀ j, raw22205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22205step0 = (fun i j => raw22205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22205step0 raw22205; decide +kernel
      have hl : raw22205step0Labels = raw22205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22205 raw22205Labels permutation434 hz
    mixedMoment B raw22205step0 raw22205step0Labels = mixedMoment B raw22205step1 raw22205step1Labels := by
      have hz : ∀ j, raw22205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22205step1 = (fun i j => raw22205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22205step1 raw22205step0; decide +kernel
      have hl : raw22205step1Labels = raw22205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22205step0 raw22205step0Labels permutation80 hz
    _ = mixedMoment B node742 node742Labels := by rfl

def raw22206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22206 raw22206Labels = mixedMoment B node740 node740Labels := by
  calc
    mixedMoment B raw22206 raw22206Labels = mixedMoment B raw22206step0 raw22206step0Labels := by
      have hz : ∀ j, raw22206 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22206step0 = (fun i j => raw22206 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22206step0 raw22206; decide +kernel
      have hl : raw22206step0Labels = raw22206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22206 raw22206Labels permutation434 hz
    mixedMoment B raw22206step0 raw22206step0Labels = mixedMoment B raw22206step1 raw22206step1Labels := by
      have hz : ∀ j, raw22206step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22206step1 = (fun i j => raw22206step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22206step1 raw22206step0; decide +kernel
      have hl : raw22206step1Labels = raw22206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22206step0 raw22206step0Labels permutation80 hz
    _ = mixedMoment B node740 node740Labels := by rfl

def raw22207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22207step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22207step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22207step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22207step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22207step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22207step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22207 raw22207Labels = mixedMoment B node4129 node4129Labels := by
  calc
    mixedMoment B raw22207 raw22207Labels = mixedMoment B raw22207step0 raw22207step0Labels := by
      have hz : ∀ j, raw22207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22207step0 = (fun i j => raw22207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22207step0 raw22207; decide +kernel
      have hl : raw22207step0Labels = raw22207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22207 raw22207Labels permutation434 hz
    mixedMoment B raw22207step0 raw22207step0Labels = mixedMoment B raw22207step1 raw22207step1Labels := by
      have hz : ∀ j, raw22207step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22207step1 = (fun i j => raw22207step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22207step1 raw22207step0; decide +kernel
      have hl : raw22207step1Labels = raw22207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22207step0 raw22207step0Labels permutation80 hz
    mixedMoment B raw22207step1 raw22207step1Labels = mixedMoment B raw22207step2 raw22207step2Labels := by
      have ha : raw22207step2 = (fun i j => raw22207step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22207step2 raw22207step1; decide +kernel
      have hl : raw22207step2Labels = raw22207step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22207step1 raw22207step1Labels permutation10 permutation4
    mixedMoment B raw22207step2 raw22207step2Labels = mixedMoment B raw22207step3 raw22207step3Labels := by
      have ha : raw22207step3 = -raw22207step2 := by apply Matrix.ext; change ∀ i j, raw22207step3 i j = -(raw22207step2 i j); unfold raw22207step3 raw22207step2; decide +kernel
      have hl : raw22207step3Labels = raw22207step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22207step3 raw22207step3Labels = mixedMoment B raw22207step4 raw22207step4Labels := by
      have ha : raw22207step4 = raw22207step3 := by apply Matrix.ext; unfold raw22207step4 raw22207step3; decide +kernel
      have hl : raw22207step3Labels = labelEmbedding7 ∘ raw22207step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22207step3 raw22207step3Labels raw22207step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4129 node4129Labels := by rfl

def raw22208 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22208step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22208step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22208 raw22208Labels = mixedMoment B node4220 node4220Labels := by
  calc
    mixedMoment B raw22208 raw22208Labels = mixedMoment B raw22208step0 raw22208step0Labels := by
      have hz : ∀ j, raw22208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22208step0 = (fun i j => raw22208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22208step0 raw22208; decide +kernel
      have hl : raw22208step0Labels = raw22208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22208 raw22208Labels permutation434 hz
    mixedMoment B raw22208step0 raw22208step0Labels = mixedMoment B raw22208step1 raw22208step1Labels := by
      have ha : raw22208step1 = (fun i j => raw22208step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22208step1 raw22208step0; decide +kernel
      have hl : raw22208step1Labels = raw22208step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22208step0 raw22208step0Labels permutation40 permutation4
    mixedMoment B raw22208step1 raw22208step1Labels = mixedMoment B raw22208step2 raw22208step2Labels := by
      have ha : raw22208step2 = -raw22208step1 := by apply Matrix.ext; change ∀ i j, raw22208step2 i j = -(raw22208step1 i j); unfold raw22208step2 raw22208step1; decide +kernel
      have hl : raw22208step2Labels = raw22208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22208step2 raw22208step2Labels = mixedMoment B raw22208step3 raw22208step3Labels := by
      have ha : raw22208step3 = raw22208step2 := by apply Matrix.ext; unfold raw22208step3 raw22208step2; decide +kernel
      have hl : raw22208step2Labels = labelEmbedding7 ∘ raw22208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22208step2 raw22208step2Labels raw22208step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4220 node4220Labels := by rfl

def raw22209 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22209step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22209step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22209step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22209step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22209 raw22209Labels = mixedMoment B node4220 node4220Labels := by
  calc
    mixedMoment B raw22209 raw22209Labels = mixedMoment B raw22209step0 raw22209step0Labels := by
      have hz : ∀ j, raw22209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22209step0 = (fun i j => raw22209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22209step0 raw22209; decide +kernel
      have hl : raw22209step0Labels = raw22209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22209 raw22209Labels permutation346 hz
    mixedMoment B raw22209step0 raw22209step0Labels = mixedMoment B raw22209step1 raw22209step1Labels := by
      have ha : raw22209step1 = (fun i j => raw22209step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22209step1 raw22209step0; decide +kernel
      have hl : raw22209step1Labels = raw22209step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22209step0 raw22209step0Labels permutation40 permutation4
    mixedMoment B raw22209step1 raw22209step1Labels = mixedMoment B raw22209step2 raw22209step2Labels := by
      have ha : raw22209step2 = -raw22209step1 := by apply Matrix.ext; change ∀ i j, raw22209step2 i j = -(raw22209step1 i j); unfold raw22209step2 raw22209step1; decide +kernel
      have hl : raw22209step2Labels = raw22209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22209step2 raw22209step2Labels = mixedMoment B raw22209step3 raw22209step3Labels := by
      have ha : raw22209step3 = raw22209step2 := by apply Matrix.ext; unfold raw22209step3 raw22209step2; decide +kernel
      have hl : raw22209step2Labels = labelEmbedding7 ∘ raw22209step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22209step2 raw22209step2Labels raw22209step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4220 node4220Labels := by rfl

def raw22210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22210step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22210step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22210step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22210step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22210 raw22210Labels = mixedMoment B node4114 node4114Labels := by
  calc
    mixedMoment B raw22210 raw22210Labels = mixedMoment B raw22210step0 raw22210step0Labels := by
      have hz : ∀ j, raw22210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22210step0 = (fun i j => raw22210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22210step0 raw22210; decide +kernel
      have hl : raw22210step0Labels = raw22210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22210 raw22210Labels permutation434 hz
    mixedMoment B raw22210step0 raw22210step0Labels = mixedMoment B raw22210step1 raw22210step1Labels := by
      have ha : raw22210step1 = (fun i j => raw22210step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22210step1 raw22210step0; decide +kernel
      have hl : raw22210step1Labels = raw22210step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22210step0 raw22210step0Labels permutation32 permutation4
    mixedMoment B raw22210step1 raw22210step1Labels = mixedMoment B raw22210step2 raw22210step2Labels := by
      have ha : raw22210step2 = -raw22210step1 := by apply Matrix.ext; change ∀ i j, raw22210step2 i j = -(raw22210step1 i j); unfold raw22210step2 raw22210step1; decide +kernel
      have hl : raw22210step2Labels = raw22210step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22210step2 raw22210step2Labels = mixedMoment B raw22210step3 raw22210step3Labels := by
      have ha : raw22210step3 = raw22210step2 := by apply Matrix.ext; unfold raw22210step3 raw22210step2; decide +kernel
      have hl : raw22210step2Labels = labelEmbedding7 ∘ raw22210step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22210step2 raw22210step2Labels raw22210step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4114 node4114Labels := by rfl

def raw22211 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22211step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22211step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22211 raw22211Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw22211 raw22211Labels = mixedMoment B raw22211step0 raw22211step0Labels := by
      have hz : ∀ j, raw22211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22211step0 = (fun i j => raw22211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22211step0 raw22211; decide +kernel
      have hl : raw22211step0Labels = raw22211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22211 raw22211Labels permutation434 hz
    mixedMoment B raw22211step0 raw22211step0Labels = mixedMoment B raw22211step1 raw22211step1Labels := by
      have hz : ∀ j, raw22211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22211step1 = (fun i j => raw22211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22211step1 raw22211step0; decide +kernel
      have hl : raw22211step1Labels = raw22211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22211step0 raw22211step0Labels permutation56 hz
    mixedMoment B raw22211step1 raw22211step1Labels = mixedMoment B raw22211step2 raw22211step2Labels := by
      have ha : raw22211step2 = (fun i j => raw22211step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22211step2 raw22211step1; decide +kernel
      have hl : raw22211step2Labels = raw22211step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22211step1 raw22211step1Labels permutation8 permutation6
    mixedMoment B raw22211step2 raw22211step2Labels = mixedMoment B raw22211step3 raw22211step3Labels := by
      have ha : raw22211step3 = raw22211step2 := by apply Matrix.ext; unfold raw22211step3 raw22211step2; decide +kernel
      have hl : raw22211step2Labels = labelEmbedding9 ∘ raw22211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22211step2 raw22211step2Labels raw22211step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4269 node4269Labels := by rfl

def raw22212 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22212step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22212step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22212step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22212step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22212 raw22212Labels = mixedMoment B node4206 node4206Labels := by
  calc
    mixedMoment B raw22212 raw22212Labels = mixedMoment B raw22212step0 raw22212step0Labels := by
      have ha : raw22212step0 = (fun i j => raw22212 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22212step0 raw22212; decide +kernel
      have hl : raw22212step0Labels = raw22212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22212 raw22212Labels permutation200 permutation4
    mixedMoment B raw22212step0 raw22212step0Labels = mixedMoment B raw22212step1 raw22212step1Labels := by
      have ha : raw22212step1 = -raw22212step0 := by apply Matrix.ext; change ∀ i j, raw22212step1 i j = -(raw22212step0 i j); unfold raw22212step1 raw22212step0; decide +kernel
      have hl : raw22212step1Labels = raw22212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22212step1 raw22212step1Labels = mixedMoment B raw22212step2 raw22212step2Labels := by
      have ha : raw22212step2 = raw22212step1 := by apply Matrix.ext; unfold raw22212step2 raw22212step1; decide +kernel
      have hl : raw22212step1Labels = labelEmbedding7 ∘ raw22212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22212step1 raw22212step1Labels raw22212step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4206 node4206Labels := by rfl

def raw22213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22213step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22213step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22213step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22213step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22213 raw22213Labels = mixedMoment B node4114 node4114Labels := by
  calc
    mixedMoment B raw22213 raw22213Labels = mixedMoment B raw22213step0 raw22213step0Labels := by
      have hz : ∀ j, raw22213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22213step0 = (fun i j => raw22213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22213step0 raw22213; decide +kernel
      have hl : raw22213step0Labels = raw22213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22213 raw22213Labels permutation346 hz
    mixedMoment B raw22213step0 raw22213step0Labels = mixedMoment B raw22213step1 raw22213step1Labels := by
      have ha : raw22213step1 = (fun i j => raw22213step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22213step1 raw22213step0; decide +kernel
      have hl : raw22213step1Labels = raw22213step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22213step0 raw22213step0Labels permutation32 permutation4
    mixedMoment B raw22213step1 raw22213step1Labels = mixedMoment B raw22213step2 raw22213step2Labels := by
      have ha : raw22213step2 = -raw22213step1 := by apply Matrix.ext; change ∀ i j, raw22213step2 i j = -(raw22213step1 i j); unfold raw22213step2 raw22213step1; decide +kernel
      have hl : raw22213step2Labels = raw22213step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22213step2 raw22213step2Labels = mixedMoment B raw22213step3 raw22213step3Labels := by
      have ha : raw22213step3 = raw22213step2 := by apply Matrix.ext; unfold raw22213step3 raw22213step2; decide +kernel
      have hl : raw22213step2Labels = labelEmbedding7 ∘ raw22213step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22213step2 raw22213step2Labels raw22213step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4114 node4114Labels := by rfl

def raw22214 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22214step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22214step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22214step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22214 raw22214Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw22214 raw22214Labels = mixedMoment B raw22214step0 raw22214step0Labels := by
      have hz : ∀ j, raw22214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22214step0 = (fun i j => raw22214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22214step0 raw22214; decide +kernel
      have hl : raw22214step0Labels = raw22214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22214 raw22214Labels permutation346 hz
    mixedMoment B raw22214step0 raw22214step0Labels = mixedMoment B raw22214step1 raw22214step1Labels := by
      have hz : ∀ j, raw22214step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22214step1 = (fun i j => raw22214step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22214step1 raw22214step0; decide +kernel
      have hl : raw22214step1Labels = raw22214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22214step0 raw22214step0Labels permutation56 hz
    mixedMoment B raw22214step1 raw22214step1Labels = mixedMoment B raw22214step2 raw22214step2Labels := by
      have ha : raw22214step2 = (fun i j => raw22214step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22214step2 raw22214step1; decide +kernel
      have hl : raw22214step2Labels = raw22214step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22214step1 raw22214step1Labels permutation8 permutation6
    mixedMoment B raw22214step2 raw22214step2Labels = mixedMoment B raw22214step3 raw22214step3Labels := by
      have ha : raw22214step3 = raw22214step2 := by apply Matrix.ext; unfold raw22214step3 raw22214step2; decide +kernel
      have hl : raw22214step2Labels = labelEmbedding9 ∘ raw22214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22214step2 raw22214step2Labels raw22214step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4269 node4269Labels := by rfl

def raw22215 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22215step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22215step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22215step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22215 raw22215Labels = mixedMoment B node4206 node4206Labels := by
  calc
    mixedMoment B raw22215 raw22215Labels = mixedMoment B raw22215step0 raw22215step0Labels := by
      have ha : raw22215step0 = (fun i j => raw22215 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22215step0 raw22215; decide +kernel
      have hl : raw22215step0Labels = raw22215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22215 raw22215Labels permutation176 permutation4
    mixedMoment B raw22215step0 raw22215step0Labels = mixedMoment B raw22215step1 raw22215step1Labels := by
      have ha : raw22215step1 = -raw22215step0 := by apply Matrix.ext; change ∀ i j, raw22215step1 i j = -(raw22215step0 i j); unfold raw22215step1 raw22215step0; decide +kernel
      have hl : raw22215step1Labels = raw22215step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22215step1 raw22215step1Labels = mixedMoment B raw22215step2 raw22215step2Labels := by
      have ha : raw22215step2 = raw22215step1 := by apply Matrix.ext; unfold raw22215step2 raw22215step1; decide +kernel
      have hl : raw22215step1Labels = labelEmbedding7 ∘ raw22215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22215step1 raw22215step1Labels raw22215step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4206 node4206Labels := by rfl

def raw22216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22216step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22216step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22216step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22216step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22216step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22216 raw22216Labels = mixedMoment B node4122 node4122Labels := by
  calc
    mixedMoment B raw22216 raw22216Labels = mixedMoment B raw22216step0 raw22216step0Labels := by
      have hz : ∀ j, raw22216 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22216step0 = (fun i j => raw22216 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22216step0 raw22216; decide +kernel
      have hl : raw22216step0Labels = raw22216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22216 raw22216Labels permutation434 hz
    mixedMoment B raw22216step0 raw22216step0Labels = mixedMoment B raw22216step1 raw22216step1Labels := by
      have hz : ∀ j, raw22216step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22216step1 = (fun i j => raw22216step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22216step1 raw22216step0; decide +kernel
      have hl : raw22216step1Labels = raw22216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22216step0 raw22216step0Labels permutation80 hz
    mixedMoment B raw22216step1 raw22216step1Labels = mixedMoment B raw22216step2 raw22216step2Labels := by
      have ha : raw22216step2 = (fun i j => raw22216step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22216step2 raw22216step1; decide +kernel
      have hl : raw22216step2Labels = raw22216step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22216step1 raw22216step1Labels permutation8 permutation4
    mixedMoment B raw22216step2 raw22216step2Labels = mixedMoment B raw22216step3 raw22216step3Labels := by
      have ha : raw22216step3 = -raw22216step2 := by apply Matrix.ext; change ∀ i j, raw22216step3 i j = -(raw22216step2 i j); unfold raw22216step3 raw22216step2; decide +kernel
      have hl : raw22216step3Labels = raw22216step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22216step3 raw22216step3Labels = mixedMoment B raw22216step4 raw22216step4Labels := by
      have ha : raw22216step4 = raw22216step3 := by apply Matrix.ext; unfold raw22216step4 raw22216step3; decide +kernel
      have hl : raw22216step3Labels = labelEmbedding7 ∘ raw22216step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22216step3 raw22216step3Labels raw22216step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4122 node4122Labels := by rfl

def raw22217 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22217step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22217step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22217step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22217step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22217 raw22217Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22217 raw22217Labels = mixedMoment B raw22217step0 raw22217step0Labels := by
      have hz : ∀ j, raw22217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22217step0 = (fun i j => raw22217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22217step0 raw22217; decide +kernel
      have hl : raw22217step0Labels = raw22217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22217 raw22217Labels permutation434 hz
    mixedMoment B raw22217step0 raw22217step0Labels = mixedMoment B raw22217step1 raw22217step1Labels := by
      have ha : raw22217step1 = (fun i j => raw22217step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22217step1 raw22217step0; decide +kernel
      have hl : raw22217step1Labels = raw22217step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22217step0 raw22217step0Labels permutation38 permutation4
    mixedMoment B raw22217step1 raw22217step1Labels = mixedMoment B raw22217step2 raw22217step2Labels := by
      have ha : raw22217step2 = -raw22217step1 := by apply Matrix.ext; change ∀ i j, raw22217step2 i j = -(raw22217step1 i j); unfold raw22217step2 raw22217step1; decide +kernel
      have hl : raw22217step2Labels = raw22217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22217step2 raw22217step2Labels = mixedMoment B raw22217step3 raw22217step3Labels := by
      have ha : raw22217step3 = raw22217step2 := by apply Matrix.ext; unfold raw22217step3 raw22217step2; decide +kernel
      have hl : raw22217step2Labels = labelEmbedding7 ∘ raw22217step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22217step2 raw22217step2Labels raw22217step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

def raw22218 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22218step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22218step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22218step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22218 raw22218Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22218 raw22218Labels = mixedMoment B raw22218step0 raw22218step0Labels := by
      have hz : ∀ j, raw22218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22218step0 = (fun i j => raw22218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22218step0 raw22218; decide +kernel
      have hl : raw22218step0Labels = raw22218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22218 raw22218Labels permutation346 hz
    mixedMoment B raw22218step0 raw22218step0Labels = mixedMoment B raw22218step1 raw22218step1Labels := by
      have ha : raw22218step1 = (fun i j => raw22218step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22218step1 raw22218step0; decide +kernel
      have hl : raw22218step1Labels = raw22218step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22218step0 raw22218step0Labels permutation38 permutation4
    mixedMoment B raw22218step1 raw22218step1Labels = mixedMoment B raw22218step2 raw22218step2Labels := by
      have ha : raw22218step2 = -raw22218step1 := by apply Matrix.ext; change ∀ i j, raw22218step2 i j = -(raw22218step1 i j); unfold raw22218step2 raw22218step1; decide +kernel
      have hl : raw22218step2Labels = raw22218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22218step2 raw22218step2Labels = mixedMoment B raw22218step3 raw22218step3Labels := by
      have ha : raw22218step3 = raw22218step2 := by apply Matrix.ext; unfold raw22218step3 raw22218step2; decide +kernel
      have hl : raw22218step2Labels = labelEmbedding7 ∘ raw22218step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22218step2 raw22218step2Labels raw22218step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

def raw22219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw22219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw22219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw22219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw22219step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22219step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22219step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22219step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22219step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22219 raw22219Labels = mixedMoment B node4120 node4120Labels := by
  calc
    mixedMoment B raw22219 raw22219Labels = mixedMoment B raw22219step0 raw22219step0Labels := by
      have hz : ∀ j, raw22219 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22219step0 = (fun i j => raw22219 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22219step0 raw22219; decide +kernel
      have hl : raw22219step0Labels = raw22219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22219 raw22219Labels permutation434 hz
    mixedMoment B raw22219step0 raw22219step0Labels = mixedMoment B raw22219step1 raw22219step1Labels := by
      have hz : ∀ j, raw22219step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22219step1 = (fun i j => raw22219step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22219step1 raw22219step0; decide +kernel
      have hl : raw22219step1Labels = raw22219step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22219step0 raw22219step0Labels permutation80 hz
    mixedMoment B raw22219step1 raw22219step1Labels = mixedMoment B raw22219step2 raw22219step2Labels := by
      have ha : raw22219step2 = (fun i j => raw22219step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22219step2 raw22219step1; decide +kernel
      have hl : raw22219step2Labels = raw22219step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22219step1 raw22219step1Labels permutation8 permutation4
    mixedMoment B raw22219step2 raw22219step2Labels = mixedMoment B raw22219step3 raw22219step3Labels := by
      have ha : raw22219step3 = -raw22219step2 := by apply Matrix.ext; change ∀ i j, raw22219step3 i j = -(raw22219step2 i j); unfold raw22219step3 raw22219step2; decide +kernel
      have hl : raw22219step3Labels = raw22219step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22219step3 raw22219step3Labels = mixedMoment B raw22219step4 raw22219step4Labels := by
      have ha : raw22219step4 = raw22219step3 := by apply Matrix.ext; unfold raw22219step4 raw22219step3; decide +kernel
      have hl : raw22219step3Labels = labelEmbedding7 ∘ raw22219step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22219step3 raw22219step3Labels raw22219step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4120 node4120Labels := by rfl

def raw22220 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw22220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw22220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw22220step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22220step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22220step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22220step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22220 raw22220Labels = mixedMoment B node4211 node4211Labels := by
  calc
    mixedMoment B raw22220 raw22220Labels = mixedMoment B raw22220step0 raw22220step0Labels := by
      have hz : ∀ j, raw22220 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22220step0 = (fun i j => raw22220 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22220step0 raw22220; decide +kernel
      have hl : raw22220step0Labels = raw22220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22220 raw22220Labels permutation434 hz
    mixedMoment B raw22220step0 raw22220step0Labels = mixedMoment B raw22220step1 raw22220step1Labels := by
      have ha : raw22220step1 = (fun i j => raw22220step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22220step1 raw22220step0; decide +kernel
      have hl : raw22220step1Labels = raw22220step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22220step0 raw22220step0Labels permutation38 permutation4
    mixedMoment B raw22220step1 raw22220step1Labels = mixedMoment B raw22220step2 raw22220step2Labels := by
      have ha : raw22220step2 = -raw22220step1 := by apply Matrix.ext; change ∀ i j, raw22220step2 i j = -(raw22220step1 i j); unfold raw22220step2 raw22220step1; decide +kernel
      have hl : raw22220step2Labels = raw22220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22220step2 raw22220step2Labels = mixedMoment B raw22220step3 raw22220step3Labels := by
      have ha : raw22220step3 = raw22220step2 := by apply Matrix.ext; unfold raw22220step3 raw22220step2; decide +kernel
      have hl : raw22220step2Labels = labelEmbedding7 ∘ raw22220step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22220step2 raw22220step2Labels raw22220step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4211 node4211Labels := by rfl

def raw22221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw22221step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw22221step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22221step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw22221step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22221 raw22221Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw22221 raw22221Labels = mixedMoment B raw22221step0 raw22221step0Labels := by
      have hz : ∀ j, raw22221 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22221step0 = (fun i j => raw22221 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22221step0 raw22221; decide +kernel
      have hl : raw22221step0Labels = raw22221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22221 raw22221Labels permutation434 hz
    mixedMoment B raw22221step0 raw22221step0Labels = mixedMoment B raw22221step1 raw22221step1Labels := by
      have hz : ∀ j, raw22221step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22221step1 = (fun i j => raw22221step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22221step1 raw22221step0; decide +kernel
      have hl : raw22221step1Labels = raw22221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22221step0 raw22221step0Labels permutation80 hz
    mixedMoment B raw22221step1 raw22221step1Labels = mixedMoment B raw22221step2 raw22221step2Labels := by
      have ha : raw22221step2 = (fun i j => raw22221step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22221step2 raw22221step1; decide +kernel
      have hl : raw22221step2Labels = raw22221step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22221step1 raw22221step1Labels permutation10 permutation7
    mixedMoment B raw22221step2 raw22221step2Labels = mixedMoment B raw22221step3 raw22221step3Labels := by
      have ha : raw22221step3 = -raw22221step2 := by apply Matrix.ext; change ∀ i j, raw22221step3 i j = -(raw22221step2 i j); unfold raw22221step3 raw22221step2; decide +kernel
      have hl : raw22221step3Labels = raw22221step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22221step3 raw22221step3Labels = mixedMoment B raw22221step4 raw22221step4Labels := by
      have ha : raw22221step4 = raw22221step3 := by apply Matrix.ext; unfold raw22221step4 raw22221step3; decide +kernel
      have hl : raw22221step3Labels = labelEmbedding10 ∘ raw22221step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22221step3 raw22221step3Labels raw22221step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

def raw22222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw22222step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22222step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22222step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22222 raw22222Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw22222 raw22222Labels = mixedMoment B raw22222step0 raw22222step0Labels := by
      have hz : ∀ j, raw22222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22222step0 = (fun i j => raw22222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22222step0 raw22222; decide +kernel
      have hl : raw22222step0Labels = raw22222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22222 raw22222Labels permutation434 hz
    mixedMoment B raw22222step0 raw22222step0Labels = mixedMoment B raw22222step1 raw22222step1Labels := by
      have ha : raw22222step1 = (fun i j => raw22222step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22222step1 raw22222step0; decide +kernel
      have hl : raw22222step1Labels = raw22222step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22222step0 raw22222step0Labels permutation40 permutation7
    mixedMoment B raw22222step1 raw22222step1Labels = mixedMoment B raw22222step2 raw22222step2Labels := by
      have ha : raw22222step2 = -raw22222step1 := by apply Matrix.ext; change ∀ i j, raw22222step2 i j = -(raw22222step1 i j); unfold raw22222step2 raw22222step1; decide +kernel
      have hl : raw22222step2Labels = raw22222step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22222step2 raw22222step2Labels = mixedMoment B raw22222step3 raw22222step3Labels := by
      have ha : raw22222step3 = raw22222step2 := by apply Matrix.ext; unfold raw22222step3 raw22222step2; decide +kernel
      have hl : raw22222step2Labels = labelEmbedding10 ∘ raw22222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22222step2 raw22222step2Labels raw22222step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw22223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw22223step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22223step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22223step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22223step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22223 raw22223Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw22223 raw22223Labels = mixedMoment B raw22223step0 raw22223step0Labels := by
      have hz : ∀ j, raw22223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22223step0 = (fun i j => raw22223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22223step0 raw22223; decide +kernel
      have hl : raw22223step0Labels = raw22223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22223 raw22223Labels permutation346 hz
    mixedMoment B raw22223step0 raw22223step0Labels = mixedMoment B raw22223step1 raw22223step1Labels := by
      have ha : raw22223step1 = (fun i j => raw22223step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22223step1 raw22223step0; decide +kernel
      have hl : raw22223step1Labels = raw22223step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22223step0 raw22223step0Labels permutation40 permutation7
    mixedMoment B raw22223step1 raw22223step1Labels = mixedMoment B raw22223step2 raw22223step2Labels := by
      have ha : raw22223step2 = -raw22223step1 := by apply Matrix.ext; change ∀ i j, raw22223step2 i j = -(raw22223step1 i j); unfold raw22223step2 raw22223step1; decide +kernel
      have hl : raw22223step2Labels = raw22223step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22223step2 raw22223step2Labels = mixedMoment B raw22223step3 raw22223step3Labels := by
      have ha : raw22223step3 = raw22223step2 := by apply Matrix.ext; unfold raw22223step3 raw22223step2; decide +kernel
      have hl : raw22223step2Labels = labelEmbedding10 ∘ raw22223step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22223step2 raw22223step2Labels raw22223step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw22224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![3, 0, -3]]
def raw22224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw22224step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw22224step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22224step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw22224step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22224step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw22224step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22224 raw22224Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw22224 raw22224Labels = mixedMoment B raw22224step0 raw22224step0Labels := by
      have hz : ∀ j, raw22224 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22224step0 = (fun i j => raw22224 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22224step0 raw22224; decide +kernel
      have hl : raw22224step0Labels = raw22224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22224 raw22224Labels permutation520 hz
    mixedMoment B raw22224step0 raw22224step0Labels = mixedMoment B raw22224step1 raw22224step1Labels := by
      have hz : ∀ j, raw22224step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22224step1 = (fun i j => raw22224step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22224step1 raw22224step0; decide +kernel
      have hl : raw22224step1Labels = raw22224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22224step0 raw22224step0Labels permutation104 hz
    mixedMoment B raw22224step1 raw22224step1Labels = mixedMoment B raw22224step2 raw22224step2Labels := by
      have hz : ∀ j, raw22224step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22224step2 = (fun i j => raw22224step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22224step2 raw22224step1; decide +kernel
      have hl : raw22224step2Labels = raw22224step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22224step1 raw22224step1Labels permutation20 hz
    mixedMoment B raw22224step2 raw22224step2Labels = mixedMoment B raw22224step3 raw22224step3Labels := by
      have ha : raw22224step3 = (fun i j => raw22224step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22224step3 raw22224step2; decide +kernel
      have hl : raw22224step3Labels = raw22224step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22224step2 raw22224step2Labels permutation2 permutation7
    mixedMoment B raw22224step3 raw22224step3Labels = mixedMoment B raw22224step4 raw22224step4Labels := by
      have ha : raw22224step4 = -raw22224step3 := by apply Matrix.ext; change ∀ i j, raw22224step4 i j = -(raw22224step3 i j); unfold raw22224step4 raw22224step3; decide +kernel
      have hl : raw22224step4Labels = raw22224step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22224step4 raw22224step4Labels = mixedMoment B raw22224step5 raw22224step5Labels := by
      have ha : raw22224step5 = raw22224step4 := by apply Matrix.ext; unfold raw22224step5 raw22224step4; decide +kernel
      have hl : raw22224step4Labels = labelEmbedding10 ∘ raw22224step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22224step4 raw22224step4Labels raw22224step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw22225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw22225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw22225step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22225step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22225step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22225step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22225 raw22225Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw22225 raw22225Labels = mixedMoment B raw22225step0 raw22225step0Labels := by
      have hz : ∀ j, raw22225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22225step0 = (fun i j => raw22225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22225step0 raw22225; decide +kernel
      have hl : raw22225step0Labels = raw22225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22225 raw22225Labels permutation434 hz
    mixedMoment B raw22225step0 raw22225step0Labels = mixedMoment B raw22225step1 raw22225step1Labels := by
      have hz : ∀ j, raw22225step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22225step1 = (fun i j => raw22225step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22225step1 raw22225step0; decide +kernel
      have hl : raw22225step1Labels = raw22225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22225step0 raw22225step0Labels permutation80 hz
    mixedMoment B raw22225step1 raw22225step1Labels = mixedMoment B raw22225step2 raw22225step2Labels := by
      have ha : raw22225step2 = (fun i j => raw22225step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22225step2 raw22225step1; decide +kernel
      have hl : raw22225step2Labels = raw22225step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22225step1 raw22225step1Labels permutation10 permutation7
    mixedMoment B raw22225step2 raw22225step2Labels = mixedMoment B raw22225step3 raw22225step3Labels := by
      have ha : raw22225step3 = -raw22225step2 := by apply Matrix.ext; change ∀ i j, raw22225step3 i j = -(raw22225step2 i j); unfold raw22225step3 raw22225step2; decide +kernel
      have hl : raw22225step3Labels = raw22225step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22225step3 raw22225step3Labels = mixedMoment B raw22225step4 raw22225step4Labels := by
      have ha : raw22225step4 = raw22225step3 := by apply Matrix.ext; unfold raw22225step4 raw22225step3; decide +kernel
      have hl : raw22225step3Labels = labelEmbedding10 ∘ raw22225step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22225step3 raw22225step3Labels raw22225step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw22226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22226step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22226 raw22226Labels = mixedMoment B node4120 node4120Labels := by
  calc
    mixedMoment B raw22226 raw22226Labels = mixedMoment B raw22226step0 raw22226step0Labels := by
      have hz : ∀ j, raw22226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22226step0 = (fun i j => raw22226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22226step0 raw22226; decide +kernel
      have hl : raw22226step0Labels = raw22226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22226 raw22226Labels permutation434 hz
    mixedMoment B raw22226step0 raw22226step0Labels = mixedMoment B raw22226step1 raw22226step1Labels := by
      have hz : ∀ j, raw22226step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22226step1 = (fun i j => raw22226step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22226step1 raw22226step0; decide +kernel
      have hl : raw22226step1Labels = raw22226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22226step0 raw22226step0Labels permutation80 hz
    mixedMoment B raw22226step1 raw22226step1Labels = mixedMoment B raw22226step2 raw22226step2Labels := by
      have ha : raw22226step2 = (fun i j => raw22226step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22226step2 raw22226step1; decide +kernel
      have hl : raw22226step2Labels = raw22226step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22226step1 raw22226step1Labels permutation10 permutation2
    _ = mixedMoment B node4120 node4120Labels := by rfl

def raw22227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22227 raw22227Labels = mixedMoment B node4211 node4211Labels := by
  calc
    mixedMoment B raw22227 raw22227Labels = mixedMoment B raw22227step0 raw22227step0Labels := by
      have hz : ∀ j, raw22227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22227step0 = (fun i j => raw22227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22227step0 raw22227; decide +kernel
      have hl : raw22227step0Labels = raw22227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22227 raw22227Labels permutation434 hz
    mixedMoment B raw22227step0 raw22227step0Labels = mixedMoment B raw22227step1 raw22227step1Labels := by
      have ha : raw22227step1 = (fun i j => raw22227step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22227step1 raw22227step0; decide +kernel
      have hl : raw22227step1Labels = raw22227step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22227step0 raw22227step0Labels permutation40 permutation2
    _ = mixedMoment B node4211 node4211Labels := by rfl

def raw22228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22228 raw22228Labels = mixedMoment B node4211 node4211Labels := by
  calc
    mixedMoment B raw22228 raw22228Labels = mixedMoment B raw22228step0 raw22228step0Labels := by
      have hz : ∀ j, raw22228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22228step0 = (fun i j => raw22228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22228step0 raw22228; decide +kernel
      have hl : raw22228step0Labels = raw22228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22228 raw22228Labels permutation346 hz
    mixedMoment B raw22228step0 raw22228step0Labels = mixedMoment B raw22228step1 raw22228step1Labels := by
      have ha : raw22228step1 = (fun i j => raw22228step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22228step1 raw22228step0; decide +kernel
      have hl : raw22228step1Labels = raw22228step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22228step0 raw22228step0Labels permutation40 permutation2
    _ = mixedMoment B node4211 node4211Labels := by rfl

def raw22229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![3, 0, -3]]
def raw22229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![3, 0, -3]]
def raw22229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw22229step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw22229step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw22229step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22229 raw22229Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw22229 raw22229Labels = mixedMoment B raw22229step0 raw22229step0Labels := by
      have hz : ∀ j, raw22229 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22229step0 = (fun i j => raw22229 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22229step0 raw22229; decide +kernel
      have hl : raw22229step0Labels = raw22229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22229 raw22229Labels permutation520 hz
    mixedMoment B raw22229step0 raw22229step0Labels = mixedMoment B raw22229step1 raw22229step1Labels := by
      have hz : ∀ j, raw22229step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22229step1 = (fun i j => raw22229step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22229step1 raw22229step0; decide +kernel
      have hl : raw22229step1Labels = raw22229step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22229step0 raw22229step0Labels permutation104 hz
    mixedMoment B raw22229step1 raw22229step1Labels = mixedMoment B raw22229step2 raw22229step2Labels := by
      have hz : ∀ j, raw22229step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22229step2 = (fun i j => raw22229step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22229step2 raw22229step1; decide +kernel
      have hl : raw22229step2Labels = raw22229step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22229step1 raw22229step1Labels permutation20 hz
    mixedMoment B raw22229step2 raw22229step2Labels = mixedMoment B raw22229step3 raw22229step3Labels := by
      have hz : ∀ i, raw22229step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw22229step3 = (fun i j => raw22229step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw22229step3 raw22229step2; decide +kernel
      have hl : raw22229step3Labels = (fun j => raw22229step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22229step2 raw22229step2Labels permutation4 hz
    mixedMoment B raw22229step3 raw22229step3Labels = mixedMoment B raw22229step4 raw22229step4Labels := by
      have ha : raw22229step4 = raw22229step3 := by apply Matrix.ext; unfold raw22229step4 raw22229step3; decide +kernel
      have hl : raw22229step3Labels = labelEmbedding2 ∘ raw22229step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22229step3 raw22229step3Labels raw22229step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw22230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw22230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw22230step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22230step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22230step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22230step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22230step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22230 raw22230Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw22230 raw22230Labels = mixedMoment B raw22230step0 raw22230step0Labels := by
      have hz : ∀ j, raw22230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22230step0 = (fun i j => raw22230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22230step0 raw22230; decide +kernel
      have hl : raw22230step0Labels = raw22230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22230 raw22230Labels permutation434 hz
    mixedMoment B raw22230step0 raw22230step0Labels = mixedMoment B raw22230step1 raw22230step1Labels := by
      have hz : ∀ j, raw22230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22230step1 = (fun i j => raw22230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22230step1 raw22230step0; decide +kernel
      have hl : raw22230step1Labels = raw22230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22230step0 raw22230step0Labels permutation80 hz
    mixedMoment B raw22230step1 raw22230step1Labels = mixedMoment B raw22230step2 raw22230step2Labels := by
      have ha : raw22230step2 = (fun i j => raw22230step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22230step2 raw22230step1; decide +kernel
      have hl : raw22230step2Labels = raw22230step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22230step1 raw22230step1Labels permutation10 permutation7
    mixedMoment B raw22230step2 raw22230step2Labels = mixedMoment B raw22230step3 raw22230step3Labels := by
      have ha : raw22230step3 = -raw22230step2 := by apply Matrix.ext; change ∀ i j, raw22230step3 i j = -(raw22230step2 i j); unfold raw22230step3 raw22230step2; decide +kernel
      have hl : raw22230step3Labels = raw22230step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22230step3 raw22230step3Labels = mixedMoment B raw22230step4 raw22230step4Labels := by
      have ha : raw22230step4 = raw22230step3 := by apply Matrix.ext; unfold raw22230step4 raw22230step3; decide +kernel
      have hl : raw22230step3Labels = labelEmbedding10 ∘ raw22230step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22230step3 raw22230step3Labels raw22230step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4269 node4269Labels := by rfl

def raw22231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22231 raw22231Labels = mixedMoment B node4099 node4099Labels := by
  calc
    mixedMoment B raw22231 raw22231Labels = mixedMoment B raw22231step0 raw22231step0Labels := by
      have hz : ∀ j, raw22231 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22231step0 = (fun i j => raw22231 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22231step0 raw22231; decide +kernel
      have hl : raw22231step0Labels = raw22231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22231 raw22231Labels permutation434 hz
    _ = mixedMoment B node4099 node4099Labels := by rfl

def raw22232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22232 raw22232Labels = mixedMoment B node4231 node4231Labels := by
  calc
    mixedMoment B raw22232 raw22232Labels = mixedMoment B raw22232step0 raw22232step0Labels := by
      have hz : ∀ j, raw22232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22232step0 = (fun i j => raw22232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22232step0 raw22232; decide +kernel
      have hl : raw22232step0Labels = raw22232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22232 raw22232Labels permutation434 hz
    _ = mixedMoment B node4231 node4231Labels := by rfl

def raw22233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22233 raw22233Labels = mixedMoment B node4195 node4195Labels := by
  calc
    mixedMoment B raw22233 raw22233Labels = mixedMoment B raw22233step0 raw22233step0Labels := by
      have ha : raw22233step0 = (fun i j => raw22233 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22233step0 raw22233; decide +kernel
      have hl : raw22233step0Labels = raw22233Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22233 raw22233Labels permutation200 permutation2
    _ = mixedMoment B node4195 node4195Labels := by rfl

def raw22234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22234 raw22234Labels = mixedMoment B node4266 node4266Labels := by
  calc
    mixedMoment B raw22234 raw22234Labels = mixedMoment B raw22234step0 raw22234step0Labels := by
      have hz : ∀ j, raw22234 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22234step0 = (fun i j => raw22234 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22234step0 raw22234; decide +kernel
      have hl : raw22234step0Labels = raw22234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22234 raw22234Labels permutation520 hz
    mixedMoment B raw22234step0 raw22234step0Labels = mixedMoment B raw22234step1 raw22234step1Labels := by
      have hz : ∀ j, raw22234step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22234step1 = (fun i j => raw22234step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22234step1 raw22234step0; decide +kernel
      have hl : raw22234step1Labels = raw22234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22234step0 raw22234step0Labels permutation104 hz
    _ = mixedMoment B node4266 node4266Labels := by rfl

def raw22235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw22235step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22235step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22235 raw22235Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw22235 raw22235Labels = mixedMoment B raw22235step0 raw22235step0Labels := by
      have hz : ∀ j, raw22235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22235step0 = (fun i j => raw22235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22235step0 raw22235; decide +kernel
      have hl : raw22235step0Labels = raw22235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22235 raw22235Labels permutation434 hz
    mixedMoment B raw22235step0 raw22235step0Labels = mixedMoment B raw22235step1 raw22235step1Labels := by
      have ha : raw22235step1 = (fun i j => raw22235step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22235step1 raw22235step0; decide +kernel
      have hl : raw22235step1Labels = raw22235step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22235step0 raw22235step0Labels permutation40 permutation7
    mixedMoment B raw22235step1 raw22235step1Labels = mixedMoment B raw22235step2 raw22235step2Labels := by
      have ha : raw22235step2 = -raw22235step1 := by apply Matrix.ext; change ∀ i j, raw22235step2 i j = -(raw22235step1 i j); unfold raw22235step2 raw22235step1; decide +kernel
      have hl : raw22235step2Labels = raw22235step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22235step2 raw22235step2Labels = mixedMoment B raw22235step3 raw22235step3Labels := by
      have ha : raw22235step3 = raw22235step2 := by apply Matrix.ext; unfold raw22235step3 raw22235step2; decide +kernel
      have hl : raw22235step2Labels = labelEmbedding10 ∘ raw22235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22235step2 raw22235step2Labels raw22235step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw22236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22236 raw22236Labels = mixedMoment B node4099 node4099Labels := by
  calc
    mixedMoment B raw22236 raw22236Labels = mixedMoment B raw22236step0 raw22236step0Labels := by
      have hz : ∀ j, raw22236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22236step0 = (fun i j => raw22236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22236step0 raw22236; decide +kernel
      have hl : raw22236step0Labels = raw22236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22236 raw22236Labels permutation346 hz
    _ = mixedMoment B node4099 node4099Labels := by rfl

def raw22237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22237 raw22237Labels = mixedMoment B node4231 node4231Labels := by
  calc
    mixedMoment B raw22237 raw22237Labels = mixedMoment B raw22237step0 raw22237step0Labels := by
      have hz : ∀ j, raw22237 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22237step0 = (fun i j => raw22237 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22237step0 raw22237; decide +kernel
      have hl : raw22237step0Labels = raw22237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22237 raw22237Labels permutation346 hz
    _ = mixedMoment B node4231 node4231Labels := by rfl

def raw22238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22238 raw22238Labels = mixedMoment B node4195 node4195Labels := by
  calc
    mixedMoment B raw22238 raw22238Labels = mixedMoment B raw22238step0 raw22238step0Labels := by
      have ha : raw22238step0 = (fun i j => raw22238 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22238step0 raw22238; decide +kernel
      have hl : raw22238step0Labels = raw22238Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22238 raw22238Labels permutation176 permutation2
    _ = mixedMoment B node4195 node4195Labels := by rfl

def raw22239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22239 raw22239Labels = mixedMoment B node4266 node4266Labels := by
  calc
    mixedMoment B raw22239 raw22239Labels = mixedMoment B raw22239step0 raw22239step0Labels := by
      have hz : ∀ j, raw22239 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22239step0 = (fun i j => raw22239 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22239step0 raw22239; decide +kernel
      have hl : raw22239step0Labels = raw22239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22239 raw22239Labels permutation520 hz
    mixedMoment B raw22239step0 raw22239step0Labels = mixedMoment B raw22239step1 raw22239step1Labels := by
      have hz : ∀ j, raw22239step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22239step1 = (fun i j => raw22239step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22239step1 raw22239step0; decide +kernel
      have hl : raw22239step1Labels = raw22239step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22239step0 raw22239step0Labels permutation80 hz
    _ = mixedMoment B node4266 node4266Labels := by rfl

def raw22240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw22240step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22240step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22240step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22240step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22240 raw22240Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw22240 raw22240Labels = mixedMoment B raw22240step0 raw22240step0Labels := by
      have hz : ∀ j, raw22240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22240step0 = (fun i j => raw22240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22240step0 raw22240; decide +kernel
      have hl : raw22240step0Labels = raw22240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22240 raw22240Labels permutation346 hz
    mixedMoment B raw22240step0 raw22240step0Labels = mixedMoment B raw22240step1 raw22240step1Labels := by
      have ha : raw22240step1 = (fun i j => raw22240step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22240step1 raw22240step0; decide +kernel
      have hl : raw22240step1Labels = raw22240step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22240step0 raw22240step0Labels permutation40 permutation7
    mixedMoment B raw22240step1 raw22240step1Labels = mixedMoment B raw22240step2 raw22240step2Labels := by
      have ha : raw22240step2 = -raw22240step1 := by apply Matrix.ext; change ∀ i j, raw22240step2 i j = -(raw22240step1 i j); unfold raw22240step2 raw22240step1; decide +kernel
      have hl : raw22240step2Labels = raw22240step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22240step2 raw22240step2Labels = mixedMoment B raw22240step3 raw22240step3Labels := by
      have ha : raw22240step3 = raw22240step2 := by apply Matrix.ext; unfold raw22240step3 raw22240step2; decide +kernel
      have hl : raw22240step2Labels = labelEmbedding10 ∘ raw22240step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22240step2 raw22240step2Labels raw22240step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw22241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22241 raw22241Labels = mixedMoment B node4109 node4109Labels := by
  calc
    mixedMoment B raw22241 raw22241Labels = mixedMoment B raw22241step0 raw22241step0Labels := by
      have hz : ∀ j, raw22241 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22241step0 = (fun i j => raw22241 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22241step0 raw22241; decide +kernel
      have hl : raw22241step0Labels = raw22241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22241 raw22241Labels permutation434 hz
    mixedMoment B raw22241step0 raw22241step0Labels = mixedMoment B raw22241step1 raw22241step1Labels := by
      have hz : ∀ j, raw22241step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22241step1 = (fun i j => raw22241step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22241step1 raw22241step0; decide +kernel
      have hl : raw22241step1Labels = raw22241step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22241step0 raw22241step0Labels permutation80 hz
    _ = mixedMoment B node4109 node4109Labels := by rfl

def raw22242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22242 raw22242Labels = mixedMoment B node4241 node4241Labels := by
  calc
    mixedMoment B raw22242 raw22242Labels = mixedMoment B raw22242step0 raw22242step0Labels := by
      have hz : ∀ j, raw22242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22242step0 = (fun i j => raw22242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22242step0 raw22242; decide +kernel
      have hl : raw22242step0Labels = raw22242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22242 raw22242Labels permutation434 hz
    mixedMoment B raw22242step0 raw22242step0Labels = mixedMoment B raw22242step1 raw22242step1Labels := by
      have hz : ∀ j, raw22242step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22242step1 = (fun i j => raw22242step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22242step1 raw22242step0; decide +kernel
      have hl : raw22242step1Labels = raw22242step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22242step0 raw22242step0Labels permutation80 hz
    _ = mixedMoment B node4241 node4241Labels := by rfl

def raw22243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22243 raw22243Labels = mixedMoment B node4203 node4203Labels := by
  calc
    mixedMoment B raw22243 raw22243Labels = mixedMoment B raw22243step0 raw22243step0Labels := by
      have hz : ∀ j, raw22243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22243step0 = (fun i j => raw22243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22243step0 raw22243; decide +kernel
      have hl : raw22243step0Labels = raw22243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22243 raw22243Labels permutation434 hz
    mixedMoment B raw22243step0 raw22243step0Labels = mixedMoment B raw22243step1 raw22243step1Labels := by
      have ha : raw22243step1 = (fun i j => raw22243step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22243step1 raw22243step0; decide +kernel
      have hl : raw22243step1Labels = raw22243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22243step0 raw22243step0Labels permutation38 permutation2
    _ = mixedMoment B node4203 node4203Labels := by rfl

def raw22244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22244 raw22244Labels = mixedMoment B node4203 node4203Labels := by
  calc
    mixedMoment B raw22244 raw22244Labels = mixedMoment B raw22244step0 raw22244step0Labels := by
      have hz : ∀ j, raw22244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22244step0 = (fun i j => raw22244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22244step0 raw22244; decide +kernel
      have hl : raw22244step0Labels = raw22244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22244 raw22244Labels permutation346 hz
    mixedMoment B raw22244step0 raw22244step0Labels = mixedMoment B raw22244step1 raw22244step1Labels := by
      have ha : raw22244step1 = (fun i j => raw22244step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22244step1 raw22244step0; decide +kernel
      have hl : raw22244step1Labels = raw22244step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22244step0 raw22244step0Labels permutation38 permutation2
    _ = mixedMoment B node4203 node4203Labels := by rfl

def raw22245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22245 raw22245Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw22245 raw22245Labels = mixedMoment B raw22245step0 raw22245step0Labels := by
      have hz : ∀ j, raw22245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22245step0 = (fun i j => raw22245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22245step0 raw22245; decide +kernel
      have hl : raw22245step0Labels = raw22245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22245 raw22245Labels permutation434 hz
    mixedMoment B raw22245step0 raw22245step0Labels = mixedMoment B raw22245step1 raw22245step1Labels := by
      have hz : ∀ j, raw22245step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22245step1 = (fun i j => raw22245step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22245step1 raw22245step0; decide +kernel
      have hl : raw22245step1Labels = raw22245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22245step0 raw22245step0Labels permutation80 hz
    _ = mixedMoment B node4272 node4272Labels := by rfl

def raw22246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22246 raw22246Labels = mixedMoment B node4103 node4103Labels := by
  calc
    mixedMoment B raw22246 raw22246Labels = mixedMoment B raw22246step0 raw22246step0Labels := by
      have hz : ∀ j, raw22246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22246step0 = (fun i j => raw22246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22246step0 raw22246; decide +kernel
      have hl : raw22246step0Labels = raw22246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22246 raw22246Labels permutation434 hz
    mixedMoment B raw22246step0 raw22246step0Labels = mixedMoment B raw22246step1 raw22246step1Labels := by
      have hz : ∀ j, raw22246step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22246step1 = (fun i j => raw22246step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22246step1 raw22246step0; decide +kernel
      have hl : raw22246step1Labels = raw22246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22246step0 raw22246step0Labels permutation80 hz
    _ = mixedMoment B node4103 node4103Labels := by rfl

def raw22247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22247 raw22247Labels = mixedMoment B node4235 node4235Labels := by
  calc
    mixedMoment B raw22247 raw22247Labels = mixedMoment B raw22247step0 raw22247step0Labels := by
      have hz : ∀ j, raw22247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22247step0 = (fun i j => raw22247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22247step0 raw22247; decide +kernel
      have hl : raw22247step0Labels = raw22247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22247 raw22247Labels permutation434 hz
    mixedMoment B raw22247step0 raw22247step0Labels = mixedMoment B raw22247step1 raw22247step1Labels := by
      have hz : ∀ j, raw22247step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22247step1 = (fun i j => raw22247step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22247step1 raw22247step0; decide +kernel
      have hl : raw22247step1Labels = raw22247step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22247step0 raw22247step0Labels permutation80 hz
    _ = mixedMoment B node4235 node4235Labels := by rfl

def raw22248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22248 raw22248Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw22248 raw22248Labels = mixedMoment B raw22248step0 raw22248step0Labels := by
      have hz : ∀ j, raw22248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22248step0 = (fun i j => raw22248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22248step0 raw22248; decide +kernel
      have hl : raw22248step0Labels = raw22248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22248 raw22248Labels permutation434 hz
    mixedMoment B raw22248step0 raw22248step0Labels = mixedMoment B raw22248step1 raw22248step1Labels := by
      have ha : raw22248step1 = (fun i j => raw22248step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22248step1 raw22248step0; decide +kernel
      have hl : raw22248step1Labels = raw22248step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22248step0 raw22248step0Labels permutation38 permutation2
    _ = mixedMoment B node4198 node4198Labels := by rfl

def raw22249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22249 raw22249Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw22249 raw22249Labels = mixedMoment B raw22249step0 raw22249step0Labels := by
      have hz : ∀ j, raw22249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22249step0 = (fun i j => raw22249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22249step0 raw22249; decide +kernel
      have hl : raw22249step0Labels = raw22249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22249 raw22249Labels permutation346 hz
    mixedMoment B raw22249step0 raw22249step0Labels = mixedMoment B raw22249step1 raw22249step1Labels := by
      have ha : raw22249step1 = (fun i j => raw22249step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22249step1 raw22249step0; decide +kernel
      have hl : raw22249step1Labels = raw22249step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22249step0 raw22249step0Labels permutation38 permutation2
    _ = mixedMoment B node4198 node4198Labels := by rfl

def raw22250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw22250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw22250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![4, -1, -3]]
def raw22250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22250step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw22250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22250 raw22250Labels = mixedMoment B node4274 node4274Labels := by
  calc
    mixedMoment B raw22250 raw22250Labels = mixedMoment B raw22250step0 raw22250step0Labels := by
      have hz : ∀ j, raw22250 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22250step0 = (fun i j => raw22250 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22250step0 raw22250; decide +kernel
      have hl : raw22250step0Labels = raw22250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22250 raw22250Labels permutation520 hz
    mixedMoment B raw22250step0 raw22250step0Labels = mixedMoment B raw22250step1 raw22250step1Labels := by
      have hz : ∀ j, raw22250step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22250step1 = (fun i j => raw22250step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22250step1 raw22250step0; decide +kernel
      have hl : raw22250step1Labels = raw22250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22250step0 raw22250step0Labels permutation104 hz
    mixedMoment B raw22250step1 raw22250step1Labels = mixedMoment B raw22250step2 raw22250step2Labels := by
      have hz : ∀ j, raw22250step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22250step2 = (fun i j => raw22250step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22250step2 raw22250step1; decide +kernel
      have hl : raw22250step2Labels = raw22250step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22250step1 raw22250step1Labels permutation20 hz
    _ = mixedMoment B node4274 node4274Labels := by rfl

def raw22251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22251step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw22251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22251 raw22251Labels = mixedMoment B node566 node566Labels := by
  calc
    mixedMoment B raw22251 raw22251Labels = mixedMoment B raw22251step0 raw22251step0Labels := by
      have hz : ∀ j, raw22251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22251step0 = (fun i j => raw22251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22251step0 raw22251; decide +kernel
      have hl : raw22251step0Labels = raw22251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22251 raw22251Labels permutation434 hz
    mixedMoment B raw22251step0 raw22251step0Labels = mixedMoment B raw22251step1 raw22251step1Labels := by
      have hz : ∀ j, raw22251step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22251step1 = (fun i j => raw22251step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22251step1 raw22251step0; decide +kernel
      have hl : raw22251step1Labels = raw22251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22251step0 raw22251step0Labels permutation80 hz
    mixedMoment B raw22251step1 raw22251step1Labels = mixedMoment B raw22251step2 raw22251step2Labels := by
      have hz : ∀ j, raw22251step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22251step2 = (fun i j => raw22251step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22251step2 raw22251step1; decide +kernel
      have hl : raw22251step2Labels = raw22251step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22251step1 raw22251step1Labels permutation14 hz
    _ = mixedMoment B node566 node566Labels := by rfl

def raw22252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22252Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22252step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22252 raw22252Labels = mixedMoment B node729 node729Labels := by
  calc
    mixedMoment B raw22252 raw22252Labels = mixedMoment B raw22252step0 raw22252step0Labels := by
      have hz : ∀ j, raw22252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22252step0 = (fun i j => raw22252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22252step0 raw22252; decide +kernel
      have hl : raw22252step0Labels = raw22252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22252 raw22252Labels permutation434 hz
    mixedMoment B raw22252step0 raw22252step0Labels = mixedMoment B raw22252step1 raw22252step1Labels := by
      have hz : ∀ j, raw22252step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22252step1 = (fun i j => raw22252step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22252step1 raw22252step0; decide +kernel
      have hl : raw22252step1Labels = raw22252step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22252step0 raw22252step0Labels permutation80 hz
    _ = mixedMoment B node729 node729Labels := by rfl

def raw22253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22253Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22253step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22253 raw22253Labels = mixedMoment B node729 node729Labels := by
  calc
    mixedMoment B raw22253 raw22253Labels = mixedMoment B raw22253step0 raw22253step0Labels := by
      have hz : ∀ j, raw22253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22253step0 = (fun i j => raw22253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22253step0 raw22253; decide +kernel
      have hl : raw22253step0Labels = raw22253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22253 raw22253Labels permutation434 hz
    mixedMoment B raw22253step0 raw22253step0Labels = mixedMoment B raw22253step1 raw22253step1Labels := by
      have hz : ∀ j, raw22253step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22253step1 = (fun i j => raw22253step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22253step1 raw22253step0; decide +kernel
      have hl : raw22253step1Labels = raw22253step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22253step0 raw22253step0Labels permutation56 hz
    _ = mixedMoment B node729 node729Labels := by rfl

def raw22254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22254 raw22254Labels = mixedMoment B node729 node729Labels := by
  calc
    mixedMoment B raw22254 raw22254Labels = mixedMoment B raw22254step0 raw22254step0Labels := by
      have hz : ∀ j, raw22254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22254step0 = (fun i j => raw22254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22254step0 raw22254; decide +kernel
      have hl : raw22254step0Labels = raw22254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22254 raw22254Labels permutation346 hz
    mixedMoment B raw22254step0 raw22254step0Labels = mixedMoment B raw22254step1 raw22254step1Labels := by
      have hz : ∀ j, raw22254step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22254step1 = (fun i j => raw22254step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22254step1 raw22254step0; decide +kernel
      have hl : raw22254step1Labels = raw22254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22254step0 raw22254step0Labels permutation56 hz
    _ = mixedMoment B node729 node729Labels := by rfl

def raw22255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -2, -1]]
def raw22255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -2, -1]]
def raw22255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, 2, -3], ![3, -2, -1]]
def raw22255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22255step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw22255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22255 raw22255Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw22255 raw22255Labels = mixedMoment B raw22255step0 raw22255step0Labels := by
      have hz : ∀ j, raw22255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22255step0 = (fun i j => raw22255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22255step0 raw22255; decide +kernel
      have hl : raw22255step0Labels = raw22255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22255 raw22255Labels permutation434 hz
    mixedMoment B raw22255step0 raw22255step0Labels = mixedMoment B raw22255step1 raw22255step1Labels := by
      have hz : ∀ j, raw22255step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22255step1 = (fun i j => raw22255step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22255step1 raw22255step0; decide +kernel
      have hl : raw22255step1Labels = raw22255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22255step0 raw22255step0Labels permutation80 hz
    mixedMoment B raw22255step1 raw22255step1Labels = mixedMoment B raw22255step2 raw22255step2Labels := by
      have hz : ∀ j, raw22255step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22255step2 = (fun i j => raw22255step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22255step2 raw22255step1; decide +kernel
      have hl : raw22255step2Labels = raw22255step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22255step1 raw22255step1Labels permutation14 hz
    _ = mixedMoment B node860 node860Labels := by rfl

def raw22256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -1, -1]]
def raw22256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -1, -1]]
def raw22256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![2, 1, -3], ![2, -1, -1]]
def raw22256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22256step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, 1, -3], ![2, -1, -1]]
def raw22256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22256step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -1, -1], ![2, 1, -3]]
def raw22256step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22256 raw22256Labels = mixedMoment B node863 node863Labels := by
  calc
    mixedMoment B raw22256 raw22256Labels = mixedMoment B raw22256step0 raw22256step0Labels := by
      have hz : ∀ j, raw22256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22256step0 = (fun i j => raw22256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22256step0 raw22256; decide +kernel
      have hl : raw22256step0Labels = raw22256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22256 raw22256Labels permutation434 hz
    mixedMoment B raw22256step0 raw22256step0Labels = mixedMoment B raw22256step1 raw22256step1Labels := by
      have hz : ∀ j, raw22256step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22256step1 = (fun i j => raw22256step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22256step1 raw22256step0; decide +kernel
      have hl : raw22256step1Labels = raw22256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22256step0 raw22256step0Labels permutation80 hz
    mixedMoment B raw22256step1 raw22256step1Labels = mixedMoment B raw22256step2 raw22256step2Labels := by
      have hz : ∀ j, raw22256step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22256step2 = (fun i j => raw22256step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22256step2 raw22256step1; decide +kernel
      have hl : raw22256step2Labels = raw22256step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22256step1 raw22256step1Labels permutation14 hz
    mixedMoment B raw22256step2 raw22256step2Labels = mixedMoment B raw22256step3 raw22256step3Labels := by
      have ha : raw22256step3 = (fun i j => raw22256step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22256step3 raw22256step2; decide +kernel
      have hl : raw22256step3Labels = raw22256step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22256step2 raw22256step2Labels permutation3 permutation2
    _ = mixedMoment B node863 node863Labels := by rfl

def raw22257 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![0, 0], ![0, 0], ![3, -3], ![1, -1]]
def raw22257Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22257step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![0, 0], ![3, -3], ![1, -1]]
def raw22257step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22257step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![0, 0], ![3, -3], ![1, -1]]
def raw22257step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22257step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![3, -3], ![1, -1]]
def raw22257step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22257step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw22257step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22257 raw22257Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw22257 raw22257Labels = mixedMoment B raw22257step0 raw22257step0Labels := by
      have hz : ∀ j, raw22257 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22257step0 = (fun i j => raw22257 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22257step0 raw22257; decide +kernel
      have hl : raw22257step0Labels = raw22257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22257 raw22257Labels permutation434 hz
    mixedMoment B raw22257step0 raw22257step0Labels = mixedMoment B raw22257step1 raw22257step1Labels := by
      have hz : ∀ j, raw22257step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22257step1 = (fun i j => raw22257step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22257step1 raw22257step0; decide +kernel
      have hl : raw22257step1Labels = raw22257step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22257step0 raw22257step0Labels permutation80 hz
    mixedMoment B raw22257step1 raw22257step1Labels = mixedMoment B raw22257step2 raw22257step2Labels := by
      have hz : ∀ j, raw22257step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22257step2 = (fun i j => raw22257step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22257step2 raw22257step1; decide +kernel
      have hl : raw22257step2Labels = raw22257step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22257step1 raw22257step1Labels permutation14 hz
    mixedMoment B raw22257step2 raw22257step2Labels = mixedMoment B raw22257step3 raw22257step3Labels := by
      have ha : raw22257step3 = (fun i j => raw22257step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22257step3 raw22257step2; decide +kernel
      have hl : raw22257step3Labels = raw22257step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22257step2 raw22257step2Labels permutation3 permutation0
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw22258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22258step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw22258step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22258step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22258step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22258step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22258step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22258 raw22258Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw22258 raw22258Labels = mixedMoment B raw22258step0 raw22258step0Labels := by
      have hz : ∀ j, raw22258 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22258step0 = (fun i j => raw22258 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22258step0 raw22258; decide +kernel
      have hl : raw22258step0Labels = raw22258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22258 raw22258Labels permutation434 hz
    mixedMoment B raw22258step0 raw22258step0Labels = mixedMoment B raw22258step1 raw22258step1Labels := by
      have hz : ∀ j, raw22258step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22258step1 = (fun i j => raw22258step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22258step1 raw22258step0; decide +kernel
      have hl : raw22258step1Labels = raw22258step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22258step0 raw22258step0Labels permutation80 hz
    mixedMoment B raw22258step1 raw22258step1Labels = mixedMoment B raw22258step2 raw22258step2Labels := by
      have ha : raw22258step2 = (fun i j => raw22258step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22258step2 raw22258step1; decide +kernel
      have hl : raw22258step2Labels = raw22258step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22258step1 raw22258step1Labels permutation8 permutation7
    mixedMoment B raw22258step2 raw22258step2Labels = mixedMoment B raw22258step3 raw22258step3Labels := by
      have ha : raw22258step3 = -raw22258step2 := by apply Matrix.ext; change ∀ i j, raw22258step3 i j = -(raw22258step2 i j); unfold raw22258step3 raw22258step2; decide +kernel
      have hl : raw22258step3Labels = raw22258step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22258step3 raw22258step3Labels = mixedMoment B raw22258step4 raw22258step4Labels := by
      have ha : raw22258step4 = raw22258step3 := by apply Matrix.ext; unfold raw22258step4 raw22258step3; decide +kernel
      have hl : raw22258step3Labels = labelEmbedding10 ∘ raw22258step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22258step3 raw22258step3Labels raw22258step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw22259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw22259step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22259step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22259step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22259step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22259 raw22259Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw22259 raw22259Labels = mixedMoment B raw22259step0 raw22259step0Labels := by
      have hz : ∀ j, raw22259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22259step0 = (fun i j => raw22259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22259step0 raw22259; decide +kernel
      have hl : raw22259step0Labels = raw22259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22259 raw22259Labels permutation434 hz
    mixedMoment B raw22259step0 raw22259step0Labels = mixedMoment B raw22259step1 raw22259step1Labels := by
      have hz : ∀ j, raw22259step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22259step1 = (fun i j => raw22259step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22259step1 raw22259step0; decide +kernel
      have hl : raw22259step1Labels = raw22259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22259step0 raw22259step0Labels permutation56 hz
    mixedMoment B raw22259step1 raw22259step1Labels = mixedMoment B raw22259step2 raw22259step2Labels := by
      have ha : raw22259step2 = (fun i j => raw22259step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22259step2 raw22259step1; decide +kernel
      have hl : raw22259step2Labels = raw22259step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22259step1 raw22259step1Labels permutation8 permutation7
    mixedMoment B raw22259step2 raw22259step2Labels = mixedMoment B raw22259step3 raw22259step3Labels := by
      have ha : raw22259step3 = -raw22259step2 := by apply Matrix.ext; change ∀ i j, raw22259step3 i j = -(raw22259step2 i j); unfold raw22259step3 raw22259step2; decide +kernel
      have hl : raw22259step3Labels = raw22259step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22259step3 raw22259step3Labels = mixedMoment B raw22259step4 raw22259step4Labels := by
      have ha : raw22259step4 = raw22259step3 := by apply Matrix.ext; unfold raw22259step4 raw22259step3; decide +kernel
      have hl : raw22259step3Labels = labelEmbedding10 ∘ raw22259step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22259step3 raw22259step3Labels raw22259step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw22260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw22260step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22260step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22260step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22260step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22260 raw22260Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw22260 raw22260Labels = mixedMoment B raw22260step0 raw22260step0Labels := by
      have hz : ∀ j, raw22260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22260step0 = (fun i j => raw22260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22260step0 raw22260; decide +kernel
      have hl : raw22260step0Labels = raw22260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22260 raw22260Labels permutation346 hz
    mixedMoment B raw22260step0 raw22260step0Labels = mixedMoment B raw22260step1 raw22260step1Labels := by
      have hz : ∀ j, raw22260step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22260step1 = (fun i j => raw22260step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22260step1 raw22260step0; decide +kernel
      have hl : raw22260step1Labels = raw22260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22260step0 raw22260step0Labels permutation56 hz
    mixedMoment B raw22260step1 raw22260step1Labels = mixedMoment B raw22260step2 raw22260step2Labels := by
      have ha : raw22260step2 = (fun i j => raw22260step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22260step2 raw22260step1; decide +kernel
      have hl : raw22260step2Labels = raw22260step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22260step1 raw22260step1Labels permutation8 permutation7
    mixedMoment B raw22260step2 raw22260step2Labels = mixedMoment B raw22260step3 raw22260step3Labels := by
      have ha : raw22260step3 = -raw22260step2 := by apply Matrix.ext; change ∀ i j, raw22260step3 i j = -(raw22260step2 i j); unfold raw22260step3 raw22260step2; decide +kernel
      have hl : raw22260step3Labels = raw22260step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22260step3 raw22260step3Labels = mixedMoment B raw22260step4 raw22260step4Labels := by
      have ha : raw22260step4 = raw22260step3 := by apply Matrix.ext; unfold raw22260step4 raw22260step3; decide +kernel
      have hl : raw22260step3Labels = labelEmbedding10 ∘ raw22260step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22260step3 raw22260step3Labels raw22260step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw22261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw22261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 2, 0], ![-2, -1, 3]]
def raw22261step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22261step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22261step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22261step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22261step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22261 raw22261Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw22261 raw22261Labels = mixedMoment B raw22261step0 raw22261step0Labels := by
      have hz : ∀ j, raw22261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22261step0 = (fun i j => raw22261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22261step0 raw22261; decide +kernel
      have hl : raw22261step0Labels = raw22261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22261 raw22261Labels permutation434 hz
    mixedMoment B raw22261step0 raw22261step0Labels = mixedMoment B raw22261step1 raw22261step1Labels := by
      have hz : ∀ j, raw22261step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22261step1 = (fun i j => raw22261step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22261step1 raw22261step0; decide +kernel
      have hl : raw22261step1Labels = raw22261step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22261step0 raw22261step0Labels permutation80 hz
    mixedMoment B raw22261step1 raw22261step1Labels = mixedMoment B raw22261step2 raw22261step2Labels := by
      have hz : ∀ j, raw22261step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22261step2 = (fun i j => raw22261step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22261step2 raw22261step1; decide +kernel
      have hl : raw22261step2Labels = raw22261step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22261step1 raw22261step1Labels permutation14 hz
    mixedMoment B raw22261step2 raw22261step2Labels = mixedMoment B raw22261step3 raw22261step3Labels := by
      have ha : raw22261step3 = (fun i j => raw22261step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22261step3 raw22261step2; decide +kernel
      have hl : raw22261step3Labels = raw22261step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22261step2 raw22261step2Labels permutation2 permutation7
    mixedMoment B raw22261step3 raw22261step3Labels = mixedMoment B raw22261step4 raw22261step4Labels := by
      have ha : raw22261step4 = -raw22261step3 := by apply Matrix.ext; change ∀ i j, raw22261step4 i j = -(raw22261step3 i j); unfold raw22261step4 raw22261step3; decide +kernel
      have hl : raw22261step4Labels = raw22261step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22261step4 raw22261step4Labels = mixedMoment B raw22261step5 raw22261step5Labels := by
      have ha : raw22261step5 = raw22261step4 := by apply Matrix.ext; unfold raw22261step5 raw22261step4; decide +kernel
      have hl : raw22261step4Labels = labelEmbedding10 ∘ raw22261step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22261step4 raw22261step4Labels raw22261step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw22262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw22262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 1, 1], ![-2, 0, 2]]
def raw22262step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22262step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22262step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22262step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22262step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22262 raw22262Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22262 raw22262Labels = mixedMoment B raw22262step0 raw22262step0Labels := by
      have hz : ∀ j, raw22262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22262step0 = (fun i j => raw22262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22262step0 raw22262; decide +kernel
      have hl : raw22262step0Labels = raw22262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22262 raw22262Labels permutation434 hz
    mixedMoment B raw22262step0 raw22262step0Labels = mixedMoment B raw22262step1 raw22262step1Labels := by
      have hz : ∀ j, raw22262step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22262step1 = (fun i j => raw22262step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22262step1 raw22262step0; decide +kernel
      have hl : raw22262step1Labels = raw22262step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22262step0 raw22262step0Labels permutation80 hz
    mixedMoment B raw22262step1 raw22262step1Labels = mixedMoment B raw22262step2 raw22262step2Labels := by
      have hz : ∀ j, raw22262step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22262step2 = (fun i j => raw22262step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22262step2 raw22262step1; decide +kernel
      have hl : raw22262step2Labels = raw22262step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22262step1 raw22262step1Labels permutation14 hz
    mixedMoment B raw22262step2 raw22262step2Labels = mixedMoment B raw22262step3 raw22262step3Labels := by
      have ha : raw22262step3 = (fun i j => raw22262step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22262step3 raw22262step2; decide +kernel
      have hl : raw22262step3Labels = raw22262step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22262step2 raw22262step2Labels permutation2 permutation7
    mixedMoment B raw22262step3 raw22262step3Labels = mixedMoment B raw22262step4 raw22262step4Labels := by
      have ha : raw22262step4 = -raw22262step3 := by apply Matrix.ext; change ∀ i j, raw22262step4 i j = -(raw22262step3 i j); unfold raw22262step4 raw22262step3; decide +kernel
      have hl : raw22262step4Labels = raw22262step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22262step4 raw22262step4Labels = mixedMoment B raw22262step5 raw22262step5Labels := by
      have ha : raw22262step5 = raw22262step4 := by apply Matrix.ext; unfold raw22262step5 raw22262step4; decide +kernel
      have hl : raw22262step4Labels = labelEmbedding10 ∘ raw22262step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22262step4 raw22262step4Labels raw22262step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

def raw22263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22263 raw22263Labels = mixedMoment B node4121 node4121Labels := by
  calc
    mixedMoment B raw22263 raw22263Labels = mixedMoment B raw22263step0 raw22263step0Labels := by
      have hz : ∀ j, raw22263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22263step0 = (fun i j => raw22263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22263step0 raw22263; decide +kernel
      have hl : raw22263step0Labels = raw22263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22263 raw22263Labels permutation434 hz
    mixedMoment B raw22263step0 raw22263step0Labels = mixedMoment B raw22263step1 raw22263step1Labels := by
      have hz : ∀ j, raw22263step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22263step1 = (fun i j => raw22263step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22263step1 raw22263step0; decide +kernel
      have hl : raw22263step1Labels = raw22263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22263step0 raw22263step0Labels permutation80 hz
    _ = mixedMoment B node4121 node4121Labels := by rfl

def raw22264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22264 raw22264Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw22264 raw22264Labels = mixedMoment B raw22264step0 raw22264step0Labels := by
      have hz : ∀ j, raw22264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22264step0 = (fun i j => raw22264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22264step0 raw22264; decide +kernel
      have hl : raw22264step0Labels = raw22264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22264 raw22264Labels permutation434 hz
    mixedMoment B raw22264step0 raw22264step0Labels = mixedMoment B raw22264step1 raw22264step1Labels := by
      have ha : raw22264step1 = (fun i j => raw22264step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22264step1 raw22264step0; decide +kernel
      have hl : raw22264step1Labels = raw22264step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22264step0 raw22264step0Labels permutation38 permutation2
    _ = mixedMoment B node4212 node4212Labels := by rfl

def raw22265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22265 raw22265Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw22265 raw22265Labels = mixedMoment B raw22265step0 raw22265step0Labels := by
      have hz : ∀ j, raw22265 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22265step0 = (fun i j => raw22265 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22265step0 raw22265; decide +kernel
      have hl : raw22265step0Labels = raw22265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22265 raw22265Labels permutation346 hz
    mixedMoment B raw22265step0 raw22265step0Labels = mixedMoment B raw22265step1 raw22265step1Labels := by
      have ha : raw22265step1 = (fun i j => raw22265step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22265step1 raw22265step0; decide +kernel
      have hl : raw22265step1Labels = raw22265step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22265step0 raw22265step0Labels permutation38 permutation2
    _ = mixedMoment B node4212 node4212Labels := by rfl

def raw22266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22266step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22266step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22266step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22266step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22266step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22266step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22266 raw22266Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw22266 raw22266Labels = mixedMoment B raw22266step0 raw22266step0Labels := by
      have hz : ∀ j, raw22266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22266step0 = (fun i j => raw22266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22266step0 raw22266; decide +kernel
      have hl : raw22266step0Labels = raw22266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22266 raw22266Labels permutation434 hz
    mixedMoment B raw22266step0 raw22266step0Labels = mixedMoment B raw22266step1 raw22266step1Labels := by
      have hz : ∀ j, raw22266step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22266step1 = (fun i j => raw22266step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22266step1 raw22266step0; decide +kernel
      have hl : raw22266step1Labels = raw22266step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22266step0 raw22266step0Labels permutation80 hz
    mixedMoment B raw22266step1 raw22266step1Labels = mixedMoment B raw22266step2 raw22266step2Labels := by
      have ha : raw22266step2 = (fun i j => raw22266step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22266step2 raw22266step1; decide +kernel
      have hl : raw22266step2Labels = raw22266step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22266step1 raw22266step1Labels permutation8 permutation7
    mixedMoment B raw22266step2 raw22266step2Labels = mixedMoment B raw22266step3 raw22266step3Labels := by
      have ha : raw22266step3 = -raw22266step2 := by apply Matrix.ext; change ∀ i j, raw22266step3 i j = -(raw22266step2 i j); unfold raw22266step3 raw22266step2; decide +kernel
      have hl : raw22266step3Labels = raw22266step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22266step3 raw22266step3Labels = mixedMoment B raw22266step4 raw22266step4Labels := by
      have ha : raw22266step4 = raw22266step3 := by apply Matrix.ext; unfold raw22266step4 raw22266step3; decide +kernel
      have hl : raw22266step3Labels = labelEmbedding10 ∘ raw22266step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22266step3 raw22266step3Labels raw22266step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

def raw22267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw22267step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22267step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22267step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22267step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22267 raw22267Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw22267 raw22267Labels = mixedMoment B raw22267step0 raw22267step0Labels := by
      have hz : ∀ j, raw22267 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22267step0 = (fun i j => raw22267 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22267step0 raw22267; decide +kernel
      have hl : raw22267step0Labels = raw22267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22267 raw22267Labels permutation434 hz
    mixedMoment B raw22267step0 raw22267step0Labels = mixedMoment B raw22267step1 raw22267step1Labels := by
      have hz : ∀ j, raw22267step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22267step1 = (fun i j => raw22267step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22267step1 raw22267step0; decide +kernel
      have hl : raw22267step1Labels = raw22267step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22267step0 raw22267step0Labels permutation80 hz
    mixedMoment B raw22267step1 raw22267step1Labels = mixedMoment B raw22267step2 raw22267step2Labels := by
      have ha : raw22267step2 = (fun i j => raw22267step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22267step2 raw22267step1; decide +kernel
      have hl : raw22267step2Labels = raw22267step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22267step1 raw22267step1Labels permutation8 permutation7
    mixedMoment B raw22267step2 raw22267step2Labels = mixedMoment B raw22267step3 raw22267step3Labels := by
      have ha : raw22267step3 = -raw22267step2 := by apply Matrix.ext; change ∀ i j, raw22267step3 i j = -(raw22267step2 i j); unfold raw22267step3 raw22267step2; decide +kernel
      have hl : raw22267step3Labels = raw22267step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22267step3 raw22267step3Labels = mixedMoment B raw22267step4 raw22267step4Labels := by
      have ha : raw22267step4 = raw22267step3 := by apply Matrix.ext; unfold raw22267step4 raw22267step3; decide +kernel
      have hl : raw22267step3Labels = labelEmbedding10 ∘ raw22267step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22267step3 raw22267step3Labels raw22267step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4273 node4273Labels := by rfl

def raw22268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22268 raw22268Labels = mixedMoment B node4121 node4121Labels := by
  calc
    mixedMoment B raw22268 raw22268Labels = mixedMoment B raw22268step0 raw22268step0Labels := by
      have hz : ∀ j, raw22268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22268step0 = (fun i j => raw22268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22268step0 raw22268; decide +kernel
      have hl : raw22268step0Labels = raw22268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22268 raw22268Labels permutation434 hz
    mixedMoment B raw22268step0 raw22268step0Labels = mixedMoment B raw22268step1 raw22268step1Labels := by
      have hz : ∀ j, raw22268step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22268step1 = (fun i j => raw22268step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22268step1 raw22268step0; decide +kernel
      have hl : raw22268step1Labels = raw22268step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22268step0 raw22268step0Labels permutation56 hz
    _ = mixedMoment B node4121 node4121Labels := by rfl

def raw22269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22269 raw22269Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw22269 raw22269Labels = mixedMoment B raw22269step0 raw22269step0Labels := by
      have hz : ∀ j, raw22269 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22269step0 = (fun i j => raw22269 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22269step0 raw22269; decide +kernel
      have hl : raw22269step0Labels = raw22269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22269 raw22269Labels permutation434 hz
    _ = mixedMoment B node4212 node4212Labels := by rfl

def raw22270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22270 raw22270Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw22270 raw22270Labels = mixedMoment B raw22270step0 raw22270step0Labels := by
      have hz : ∀ j, raw22270 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22270step0 = (fun i j => raw22270 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22270step0 raw22270; decide +kernel
      have hl : raw22270step0Labels = raw22270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22270 raw22270Labels permutation265 hz
    mixedMoment B raw22270step0 raw22270step0Labels = mixedMoment B raw22270step1 raw22270step1Labels := by
      have ha : raw22270step1 = (fun i j => raw22270step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22270step1 raw22270step0; decide +kernel
      have hl : raw22270step1Labels = raw22270step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22270step0 raw22270step0Labels permutation38 permutation2
    _ = mixedMoment B node4212 node4212Labels := by rfl

def raw22271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22271step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22271step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22271step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22271step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22271step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22271 raw22271Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw22271 raw22271Labels = mixedMoment B raw22271step0 raw22271step0Labels := by
      have hz : ∀ j, raw22271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22271step0 = (fun i j => raw22271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22271step0 raw22271; decide +kernel
      have hl : raw22271step0Labels = raw22271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22271 raw22271Labels permutation434 hz
    mixedMoment B raw22271step0 raw22271step0Labels = mixedMoment B raw22271step1 raw22271step1Labels := by
      have hz : ∀ j, raw22271step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22271step1 = (fun i j => raw22271step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22271step1 raw22271step0; decide +kernel
      have hl : raw22271step1Labels = raw22271step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22271step0 raw22271step0Labels permutation56 hz
    mixedMoment B raw22271step1 raw22271step1Labels = mixedMoment B raw22271step2 raw22271step2Labels := by
      have ha : raw22271step2 = (fun i j => raw22271step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22271step2 raw22271step1; decide +kernel
      have hl : raw22271step2Labels = raw22271step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22271step1 raw22271step1Labels permutation8 permutation7
    mixedMoment B raw22271step2 raw22271step2Labels = mixedMoment B raw22271step3 raw22271step3Labels := by
      have ha : raw22271step3 = -raw22271step2 := by apply Matrix.ext; change ∀ i j, raw22271step3 i j = -(raw22271step2 i j); unfold raw22271step3 raw22271step2; decide +kernel
      have hl : raw22271step3Labels = raw22271step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22271step3 raw22271step3Labels = mixedMoment B raw22271step4 raw22271step4Labels := by
      have ha : raw22271step4 = raw22271step3 := by apply Matrix.ext; unfold raw22271step4 raw22271step3; decide +kernel
      have hl : raw22271step3Labels = labelEmbedding10 ∘ raw22271step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22271step3 raw22271step3Labels raw22271step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
