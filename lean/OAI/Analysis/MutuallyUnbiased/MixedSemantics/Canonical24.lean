import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3072step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3072step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw3072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3072 raw3072Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw3072 raw3072Labels = mixedMoment B raw3072step0 raw3072step0Labels := by
      have hz : ∀ j, raw3072 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3072step0 = (fun i j => raw3072 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3072step0 raw3072; decide +kernel
      have hl : raw3072step0Labels = raw3072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3072 raw3072Labels permutation520 hz
    mixedMoment B raw3072step0 raw3072step0Labels = mixedMoment B raw3072step1 raw3072step1Labels := by
      have hz : ∀ j, raw3072step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3072step1 = (fun i j => raw3072step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3072step1 raw3072step0; decide +kernel
      have hl : raw3072step1Labels = raw3072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3072step0 raw3072step0Labels permutation104 hz
    mixedMoment B raw3072step1 raw3072step1Labels = mixedMoment B raw3072step2 raw3072step2Labels := by
      have ha : raw3072step2 = (fun i j => raw3072step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3072step2 raw3072step1; decide +kernel
      have hl : raw3072step2Labels = raw3072step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3072step1 raw3072step1Labels permutation9 permutation3
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw3073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw3073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3073 raw3073Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw3073 raw3073Labels = mixedMoment B raw3073step0 raw3073step0Labels := by
      have hz : ∀ j, raw3073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3073step0 = (fun i j => raw3073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3073step0 raw3073; decide +kernel
      have hl : raw3073step0Labels = raw3073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3073 raw3073Labels permutation434 hz
    mixedMoment B raw3073step0 raw3073step0Labels = mixedMoment B raw3073step1 raw3073step1Labels := by
      have ha : raw3073step1 = (fun i j => raw3073step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3073step1 raw3073step0; decide +kernel
      have hl : raw3073step1Labels = raw3073step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3073step0 raw3073step0Labels permutation144 permutation6
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw3074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3074 raw3074Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw3074 raw3074Labels = mixedMoment B raw3074step0 raw3074step0Labels := by
      have hz : ∀ j, raw3074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3074step0 = (fun i j => raw3074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3074step0 raw3074; decide +kernel
      have hl : raw3074step0Labels = raw3074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3074 raw3074Labels permutation346 hz
    mixedMoment B raw3074step0 raw3074step0Labels = mixedMoment B raw3074step1 raw3074step1Labels := by
      have ha : raw3074step1 = (fun i j => raw3074step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3074step1 raw3074step0; decide +kernel
      have hl : raw3074step1Labels = raw3074step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3074step0 raw3074step0Labels permutation36 permutation3
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw3075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3075step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3075 raw3075Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw3075 raw3075Labels = mixedMoment B raw3075step0 raw3075step0Labels := by
      have hz : ∀ j, raw3075 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3075step0 = (fun i j => raw3075 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3075step0 raw3075; decide +kernel
      have hl : raw3075step0Labels = raw3075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3075 raw3075Labels permutation346 hz
    mixedMoment B raw3075step0 raw3075step0Labels = mixedMoment B raw3075step1 raw3075step1Labels := by
      have ha : raw3075step1 = (fun i j => raw3075step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3075step1 raw3075step0; decide +kernel
      have hl : raw3075step1Labels = raw3075step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3075step0 raw3075step0Labels permutation36 permutation3
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw3076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3076 raw3076Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw3076 raw3076Labels = mixedMoment B raw3076step0 raw3076step0Labels := by
      have ha : raw3076step0 = (fun i j => raw3076 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3076step0 raw3076; decide +kernel
      have hl : raw3076step0Labels = raw3076Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3076 raw3076Labels permutation180 permutation3
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw3077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3077step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3077step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3077step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw3077step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3077 raw3077Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw3077 raw3077Labels = mixedMoment B raw3077step0 raw3077step0Labels := by
      have hz : ∀ j, raw3077 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3077step0 = (fun i j => raw3077 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3077step0 raw3077; decide +kernel
      have hl : raw3077step0Labels = raw3077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3077 raw3077Labels permutation520 hz
    mixedMoment B raw3077step0 raw3077step0Labels = mixedMoment B raw3077step1 raw3077step1Labels := by
      have hz : ∀ j, raw3077step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3077step1 = (fun i j => raw3077step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3077step1 raw3077step0; decide +kernel
      have hl : raw3077step1Labels = raw3077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3077step0 raw3077step0Labels permutation80 hz
    mixedMoment B raw3077step1 raw3077step1Labels = mixedMoment B raw3077step2 raw3077step2Labels := by
      have ha : raw3077step2 = (fun i j => raw3077step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3077step2 raw3077step1; decide +kernel
      have hl : raw3077step2Labels = raw3077step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3077step1 raw3077step1Labels permutation9 permutation3
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw3078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3078step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw3078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3078 raw3078Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw3078 raw3078Labels = mixedMoment B raw3078step0 raw3078step0Labels := by
      have hz : ∀ j, raw3078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3078step0 = (fun i j => raw3078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3078step0 raw3078; decide +kernel
      have hl : raw3078step0Labels = raw3078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3078 raw3078Labels permutation346 hz
    mixedMoment B raw3078step0 raw3078step0Labels = mixedMoment B raw3078step1 raw3078step1Labels := by
      have ha : raw3078step1 = (fun i j => raw3078step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3078step1 raw3078step0; decide +kernel
      have hl : raw3078step1Labels = raw3078step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3078step0 raw3078step0Labels permutation144 permutation6
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw3079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw3079step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw3079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3079 raw3079Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw3079 raw3079Labels = mixedMoment B raw3079step0 raw3079step0Labels := by
      have hz : ∀ j, raw3079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3079step0 = (fun i j => raw3079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3079step0 raw3079; decide +kernel
      have hl : raw3079step0Labels = raw3079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3079 raw3079Labels permutation434 hz
    mixedMoment B raw3079step0 raw3079step0Labels = mixedMoment B raw3079step1 raw3079step1Labels := by
      have hz : ∀ j, raw3079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3079step1 = (fun i j => raw3079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3079step1 raw3079step0; decide +kernel
      have hl : raw3079step1Labels = raw3079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3079step0 raw3079step0Labels permutation80 hz
    mixedMoment B raw3079step1 raw3079step1Labels = mixedMoment B raw3079step2 raw3079step2Labels := by
      have ha : raw3079step2 = (fun i j => raw3079step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3079step2 raw3079step1; decide +kernel
      have hl : raw3079step2Labels = raw3079step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3079step1 raw3079step1Labels permutation9 permutation3
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw3080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3080step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2]]
def raw3080step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3080step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3080step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3080step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3080 raw3080Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw3080 raw3080Labels = mixedMoment B raw3080step0 raw3080step0Labels := by
      have hz : ∀ j, raw3080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3080step0 = (fun i j => raw3080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3080step0 raw3080; decide +kernel
      have hl : raw3080step0Labels = raw3080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3080 raw3080Labels permutation434 hz
    mixedMoment B raw3080step0 raw3080step0Labels = mixedMoment B raw3080step1 raw3080step1Labels := by
      have hz : ∀ j, raw3080step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3080step1 = (fun i j => raw3080step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3080step1 raw3080step0; decide +kernel
      have hl : raw3080step1Labels = raw3080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3080step0 raw3080step0Labels permutation80 hz
    mixedMoment B raw3080step1 raw3080step1Labels = mixedMoment B raw3080step2 raw3080step2Labels := by
      have ha : raw3080step2 = (fun i j => raw3080step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3080step2 raw3080step1; decide +kernel
      have hl : raw3080step2Labels = raw3080step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3080step1 raw3080step1Labels permutation25 permutation3
    mixedMoment B raw3080step2 raw3080step2Labels = mixedMoment B raw3080step3 raw3080step3Labels := by
      have ha : raw3080step3 = -raw3080step2 := by apply Matrix.ext; change ∀ i j, raw3080step3 i j = -(raw3080step2 i j); unfold raw3080step3 raw3080step2; decide +kernel
      have hl : raw3080step3Labels = raw3080step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw3081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3081step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3081 raw3081Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw3081 raw3081Labels = mixedMoment B raw3081step0 raw3081step0Labels := by
      have hz : ∀ j, raw3081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3081step0 = (fun i j => raw3081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3081step0 raw3081; decide +kernel
      have hl : raw3081step0Labels = raw3081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3081 raw3081Labels permutation434 hz
    mixedMoment B raw3081step0 raw3081step0Labels = mixedMoment B raw3081step1 raw3081step1Labels := by
      have ha : raw3081step1 = (fun i j => raw3081step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3081step1 raw3081step0; decide +kernel
      have hl : raw3081step1Labels = raw3081step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3081step0 raw3081step0Labels permutation125 permutation3
    mixedMoment B raw3081step1 raw3081step1Labels = mixedMoment B raw3081step2 raw3081step2Labels := by
      have ha : raw3081step2 = -raw3081step1 := by apply Matrix.ext; change ∀ i j, raw3081step2 i j = -(raw3081step1 i j); unfold raw3081step2 raw3081step1; decide +kernel
      have hl : raw3081step2Labels = raw3081step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw3082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3082 raw3082Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw3082 raw3082Labels = mixedMoment B raw3082step0 raw3082step0Labels := by
      have hz : ∀ j, raw3082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3082step0 = (fun i j => raw3082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3082step0 raw3082; decide +kernel
      have hl : raw3082step0Labels = raw3082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3082 raw3082Labels permutation346 hz
    mixedMoment B raw3082step0 raw3082step0Labels = mixedMoment B raw3082step1 raw3082step1Labels := by
      have ha : raw3082step1 = (fun i j => raw3082step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3082step1 raw3082step0; decide +kernel
      have hl : raw3082step1Labels = raw3082step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3082step0 raw3082step0Labels permutation125 permutation3
    mixedMoment B raw3082step1 raw3082step1Labels = mixedMoment B raw3082step2 raw3082step2Labels := by
      have ha : raw3082step2 = -raw3082step1 := by apply Matrix.ext; change ∀ i j, raw3082step2 i j = -(raw3082step1 i j); unfold raw3082step2 raw3082step1; decide +kernel
      have hl : raw3082step2Labels = raw3082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw3083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2]]
def raw3083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2]]
def raw3083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![0, 2, -2]]
def raw3083step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw3083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3083step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3083 raw3083Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw3083 raw3083Labels = mixedMoment B raw3083step0 raw3083step0Labels := by
      have hz : ∀ j, raw3083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3083step0 = (fun i j => raw3083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3083step0 raw3083; decide +kernel
      have hl : raw3083step0Labels = raw3083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3083 raw3083Labels permutation434 hz
    mixedMoment B raw3083step0 raw3083step0Labels = mixedMoment B raw3083step1 raw3083step1Labels := by
      have hz : ∀ j, raw3083step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3083step1 = (fun i j => raw3083step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3083step1 raw3083step0; decide +kernel
      have hl : raw3083step1Labels = raw3083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3083step0 raw3083step0Labels permutation80 hz
    mixedMoment B raw3083step1 raw3083step1Labels = mixedMoment B raw3083step2 raw3083step2Labels := by
      have ha : raw3083step2 = (fun i j => raw3083step1 (permutation23 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3083step2 raw3083step1; decide +kernel
      have hl : raw3083step2Labels = raw3083step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3083step1 raw3083step1Labels permutation23 permutation3
    mixedMoment B raw3083step2 raw3083step2Labels = mixedMoment B raw3083step3 raw3083step3Labels := by
      have ha : raw3083step3 = -raw3083step2 := by apply Matrix.ext; change ∀ i j, raw3083step3 i j = -(raw3083step2 i j); unfold raw3083step3 raw3083step2; decide +kernel
      have hl : raw3083step3Labels = raw3083step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw3084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw3084step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3084 raw3084Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw3084 raw3084Labels = mixedMoment B raw3084step0 raw3084step0Labels := by
      have hz : ∀ j, raw3084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3084step0 = (fun i j => raw3084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3084step0 raw3084; decide +kernel
      have hl : raw3084step0Labels = raw3084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3084 raw3084Labels permutation434 hz
    mixedMoment B raw3084step0 raw3084step0Labels = mixedMoment B raw3084step1 raw3084step1Labels := by
      have hz : ∀ j, raw3084step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3084step1 = (fun i j => raw3084step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3084step1 raw3084step0; decide +kernel
      have hl : raw3084step1Labels = raw3084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3084step0 raw3084step0Labels permutation80 hz
    mixedMoment B raw3084step1 raw3084step1Labels = mixedMoment B raw3084step2 raw3084step2Labels := by
      have ha : raw3084step2 = (fun i j => raw3084step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3084step2 raw3084step1; decide +kernel
      have hl : raw3084step2Labels = raw3084step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3084step1 raw3084step1Labels permutation8 permutation3
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw3085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3085step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw3085step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3085 raw3085Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw3085 raw3085Labels = mixedMoment B raw3085step0 raw3085step0Labels := by
      have hz : ∀ j, raw3085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3085step0 = (fun i j => raw3085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3085step0 raw3085; decide +kernel
      have hl : raw3085step0Labels = raw3085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3085 raw3085Labels permutation434 hz
    mixedMoment B raw3085step0 raw3085step0Labels = mixedMoment B raw3085step1 raw3085step1Labels := by
      have hz : ∀ j, raw3085step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3085step1 = (fun i j => raw3085step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3085step1 raw3085step0; decide +kernel
      have hl : raw3085step1Labels = raw3085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3085step0 raw3085step0Labels permutation80 hz
    mixedMoment B raw3085step1 raw3085step1Labels = mixedMoment B raw3085step2 raw3085step2Labels := by
      have ha : raw3085step2 = (fun i j => raw3085step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3085step2 raw3085step1; decide +kernel
      have hl : raw3085step2Labels = raw3085step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3085step1 raw3085step1Labels permutation8 permutation3
    _ = mixedMoment B node4001 node4001Labels := by rfl

def raw3086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3086Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3086step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3086 raw3086Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw3086 raw3086Labels = mixedMoment B raw3086step0 raw3086step0Labels := by
      have hz : ∀ j, raw3086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3086step0 = (fun i j => raw3086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3086step0 raw3086; decide +kernel
      have hl : raw3086step0Labels = raw3086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3086 raw3086Labels permutation434 hz
    mixedMoment B raw3086step0 raw3086step0Labels = mixedMoment B raw3086step1 raw3086step1Labels := by
      have ha : raw3086step1 = (fun i j => raw3086step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3086step1 raw3086step0; decide +kernel
      have hl : raw3086step1Labels = raw3086step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3086step0 raw3086step0Labels permutation38 permutation3
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw3087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3087Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3087step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3087 raw3087Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw3087 raw3087Labels = mixedMoment B raw3087step0 raw3087step0Labels := by
      have hz : ∀ j, raw3087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3087step0 = (fun i j => raw3087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3087step0 raw3087; decide +kernel
      have hl : raw3087step0Labels = raw3087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3087 raw3087Labels permutation346 hz
    mixedMoment B raw3087step0 raw3087step0Labels = mixedMoment B raw3087step1 raw3087step1Labels := by
      have ha : raw3087step1 = (fun i j => raw3087step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3087step1 raw3087step0; decide +kernel
      have hl : raw3087step1Labels = raw3087step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3087step0 raw3087step0Labels permutation38 permutation3
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw3088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw3088Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw3088step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw3088step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3088step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw3088step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3088step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw3088step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3088 raw3088Labels = mixedMoment B node4019 node4019Labels := by
  calc
    mixedMoment B raw3088 raw3088Labels = mixedMoment B raw3088step0 raw3088step0Labels := by
      have hz : ∀ j, raw3088 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3088step0 = (fun i j => raw3088 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3088step0 raw3088; decide +kernel
      have hl : raw3088step0Labels = raw3088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3088 raw3088Labels permutation520 hz
    mixedMoment B raw3088step0 raw3088step0Labels = mixedMoment B raw3088step1 raw3088step1Labels := by
      have hz : ∀ j, raw3088step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3088step1 = (fun i j => raw3088step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3088step1 raw3088step0; decide +kernel
      have hl : raw3088step1Labels = raw3088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3088step0 raw3088step0Labels permutation104 hz
    mixedMoment B raw3088step1 raw3088step1Labels = mixedMoment B raw3088step2 raw3088step2Labels := by
      have hz : ∀ j, raw3088step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3088step2 = (fun i j => raw3088step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3088step2 raw3088step1; decide +kernel
      have hl : raw3088step2Labels = raw3088step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3088step1 raw3088step1Labels permutation20 hz
    mixedMoment B raw3088step2 raw3088step2Labels = mixedMoment B raw3088step3 raw3088step3Labels := by
      have ha : raw3088step3 = (fun i j => raw3088step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3088step3 raw3088step2; decide +kernel
      have hl : raw3088step3Labels = raw3088step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3088step2 raw3088step2Labels permutation2 permutation3
    _ = mixedMoment B node4019 node4019Labels := by rfl

def raw3089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1]]
def raw3089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3089step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3089step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3089 raw3089Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw3089 raw3089Labels = mixedMoment B raw3089step0 raw3089step0Labels := by
      have hz : ∀ j, raw3089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3089step0 = (fun i j => raw3089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3089step0 raw3089; decide +kernel
      have hl : raw3089step0Labels = raw3089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3089 raw3089Labels permutation434 hz
    mixedMoment B raw3089step0 raw3089step0Labels = mixedMoment B raw3089step1 raw3089step1Labels := by
      have hz : ∀ j, raw3089step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3089step1 = (fun i j => raw3089step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3089step1 raw3089step0; decide +kernel
      have hl : raw3089step1Labels = raw3089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3089step0 raw3089step0Labels permutation80 hz
    mixedMoment B raw3089step1 raw3089step1Labels = mixedMoment B raw3089step2 raw3089step2Labels := by
      have ha : raw3089step2 = (fun i j => raw3089step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3089step2 raw3089step1; decide +kernel
      have hl : raw3089step2Labels = raw3089step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3089step1 raw3089step1Labels permutation27 permutation4
    mixedMoment B raw3089step2 raw3089step2Labels = mixedMoment B raw3089step3 raw3089step3Labels := by
      have ha : raw3089step3 = raw3089step2 := by apply Matrix.ext; unfold raw3089step3 raw3089step2; decide +kernel
      have hl : raw3089step2Labels = labelEmbedding7 ∘ raw3089step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3089step2 raw3089step2Labels raw3089step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw3090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3090step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3090 raw3090Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3090 raw3090Labels = mixedMoment B raw3090step0 raw3090step0Labels := by
      have hz : ∀ j, raw3090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3090step0 = (fun i j => raw3090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3090step0 raw3090; decide +kernel
      have hl : raw3090step0Labels = raw3090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3090 raw3090Labels permutation434 hz
    mixedMoment B raw3090step0 raw3090step0Labels = mixedMoment B raw3090step1 raw3090step1Labels := by
      have ha : raw3090step1 = (fun i j => raw3090step0 (permutation133 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3090step1 raw3090step0; decide +kernel
      have hl : raw3090step1Labels = raw3090step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3090step0 raw3090step0Labels permutation133 permutation4
    mixedMoment B raw3090step1 raw3090step1Labels = mixedMoment B raw3090step2 raw3090step2Labels := by
      have ha : raw3090step2 = raw3090step1 := by apply Matrix.ext; unfold raw3090step2 raw3090step1; decide +kernel
      have hl : raw3090step1Labels = labelEmbedding7 ∘ raw3090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3090step1 raw3090step1Labels raw3090step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3091step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3091 raw3091Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3091 raw3091Labels = mixedMoment B raw3091step0 raw3091step0Labels := by
      have hz : ∀ j, raw3091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3091step0 = (fun i j => raw3091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3091step0 raw3091; decide +kernel
      have hl : raw3091step0Labels = raw3091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3091 raw3091Labels permutation346 hz
    mixedMoment B raw3091step0 raw3091step0Labels = mixedMoment B raw3091step1 raw3091step1Labels := by
      have ha : raw3091step1 = (fun i j => raw3091step0 (permutation133 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3091step1 raw3091step0; decide +kernel
      have hl : raw3091step1Labels = raw3091step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3091step0 raw3091step0Labels permutation133 permutation4
    mixedMoment B raw3091step1 raw3091step1Labels = mixedMoment B raw3091step2 raw3091step2Labels := by
      have ha : raw3091step2 = raw3091step1 := by apply Matrix.ext; unfold raw3091step2 raw3091step1; decide +kernel
      have hl : raw3091step1Labels = labelEmbedding7 ∘ raw3091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3091step1 raw3091step1Labels raw3091step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw3092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3092step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3092step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3092 raw3092Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw3092 raw3092Labels = mixedMoment B raw3092step0 raw3092step0Labels := by
      have hz : ∀ j, raw3092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3092step0 = (fun i j => raw3092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3092step0 raw3092; decide +kernel
      have hl : raw3092step0Labels = raw3092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3092 raw3092Labels permutation434 hz
    mixedMoment B raw3092step0 raw3092step0Labels = mixedMoment B raw3092step1 raw3092step1Labels := by
      have hz : ∀ j, raw3092step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3092step1 = (fun i j => raw3092step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3092step1 raw3092step0; decide +kernel
      have hl : raw3092step1Labels = raw3092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3092step0 raw3092step0Labels permutation80 hz
    mixedMoment B raw3092step1 raw3092step1Labels = mixedMoment B raw3092step2 raw3092step2Labels := by
      have ha : raw3092step2 = (fun i j => raw3092step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3092step2 raw3092step1; decide +kernel
      have hl : raw3092step2Labels = raw3092step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3092step1 raw3092step1Labels permutation26 permutation4
    mixedMoment B raw3092step2 raw3092step2Labels = mixedMoment B raw3092step3 raw3092step3Labels := by
      have ha : raw3092step3 = raw3092step2 := by apply Matrix.ext; unfold raw3092step3 raw3092step2; decide +kernel
      have hl : raw3092step2Labels = labelEmbedding7 ∘ raw3092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3092step2 raw3092step2Labels raw3092step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw3093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw3093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3093step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3093step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3093step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3093 raw3093Labels = mixedMoment B node5501 node5501Labels := by
  calc
    mixedMoment B raw3093 raw3093Labels = mixedMoment B raw3093step0 raw3093step0Labels := by
      have hz : ∀ j, raw3093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3093step0 = (fun i j => raw3093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3093step0 raw3093; decide +kernel
      have hl : raw3093step0Labels = raw3093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3093 raw3093Labels permutation434 hz
    mixedMoment B raw3093step0 raw3093step0Labels = mixedMoment B raw3093step1 raw3093step1Labels := by
      have hz : ∀ j, raw3093step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3093step1 = (fun i j => raw3093step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3093step1 raw3093step0; decide +kernel
      have hl : raw3093step1Labels = raw3093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3093step0 raw3093step0Labels permutation80 hz
    mixedMoment B raw3093step1 raw3093step1Labels = mixedMoment B raw3093step2 raw3093step2Labels := by
      have ha : raw3093step2 = (fun i j => raw3093step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3093step2 raw3093step1; decide +kernel
      have hl : raw3093step2Labels = raw3093step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3093step1 raw3093step1Labels permutation16 permutation6
    mixedMoment B raw3093step2 raw3093step2Labels = mixedMoment B raw3093step3 raw3093step3Labels := by
      have ha : raw3093step3 = raw3093step2 := by apply Matrix.ext; unfold raw3093step3 raw3093step2; decide +kernel
      have hl : raw3093step2Labels = labelEmbedding9 ∘ raw3093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3093step2 raw3093step2Labels raw3093step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5501 node5501Labels := by rfl

def raw3094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw3094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3094step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3094step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3094step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3094 raw3094Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw3094 raw3094Labels = mixedMoment B raw3094step0 raw3094step0Labels := by
      have hz : ∀ j, raw3094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3094step0 = (fun i j => raw3094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3094step0 raw3094; decide +kernel
      have hl : raw3094step0Labels = raw3094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3094 raw3094Labels permutation434 hz
    mixedMoment B raw3094step0 raw3094step0Labels = mixedMoment B raw3094step1 raw3094step1Labels := by
      have hz : ∀ j, raw3094step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3094step1 = (fun i j => raw3094step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3094step1 raw3094step0; decide +kernel
      have hl : raw3094step1Labels = raw3094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3094step0 raw3094step0Labels permutation80 hz
    mixedMoment B raw3094step1 raw3094step1Labels = mixedMoment B raw3094step2 raw3094step2Labels := by
      have ha : raw3094step2 = (fun i j => raw3094step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3094step2 raw3094step1; decide +kernel
      have hl : raw3094step2Labels = raw3094step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3094step1 raw3094step1Labels permutation8 permutation3
    mixedMoment B raw3094step2 raw3094step2Labels = mixedMoment B raw3094step3 raw3094step3Labels := by
      have ha : raw3094step3 = raw3094step2 := by apply Matrix.ext; unfold raw3094step3 raw3094step2; decide +kernel
      have hl : raw3094step2Labels = labelEmbedding6 ∘ raw3094step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3094step2 raw3094step2Labels raw3094step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw3095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3095step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3095step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3095 raw3095Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3095 raw3095Labels = mixedMoment B raw3095step0 raw3095step0Labels := by
      have hz : ∀ j, raw3095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3095step0 = (fun i j => raw3095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3095step0 raw3095; decide +kernel
      have hl : raw3095step0Labels = raw3095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3095 raw3095Labels permutation434 hz
    mixedMoment B raw3095step0 raw3095step0Labels = mixedMoment B raw3095step1 raw3095step1Labels := by
      have ha : raw3095step1 = (fun i j => raw3095step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3095step1 raw3095step0; decide +kernel
      have hl : raw3095step1Labels = raw3095step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3095step0 raw3095step0Labels permutation38 permutation3
    mixedMoment B raw3095step1 raw3095step1Labels = mixedMoment B raw3095step2 raw3095step2Labels := by
      have ha : raw3095step2 = raw3095step1 := by apply Matrix.ext; unfold raw3095step2 raw3095step1; decide +kernel
      have hl : raw3095step1Labels = labelEmbedding6 ∘ raw3095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3095step1 raw3095step1Labels raw3095step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3096step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3096step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3096 raw3096Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3096 raw3096Labels = mixedMoment B raw3096step0 raw3096step0Labels := by
      have hz : ∀ j, raw3096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3096step0 = (fun i j => raw3096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3096step0 raw3096; decide +kernel
      have hl : raw3096step0Labels = raw3096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3096 raw3096Labels permutation346 hz
    mixedMoment B raw3096step0 raw3096step0Labels = mixedMoment B raw3096step1 raw3096step1Labels := by
      have ha : raw3096step1 = (fun i j => raw3096step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3096step1 raw3096step0; decide +kernel
      have hl : raw3096step1Labels = raw3096step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3096step0 raw3096step0Labels permutation38 permutation3
    mixedMoment B raw3096step1 raw3096step1Labels = mixedMoment B raw3096step2 raw3096step2Labels := by
      have ha : raw3096step2 = raw3096step1 := by apply Matrix.ext; unfold raw3096step2 raw3096step1; decide +kernel
      have hl : raw3096step1Labels = labelEmbedding6 ∘ raw3096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3096step1 raw3096step1Labels raw3096step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw3097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3097step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3097step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3097 raw3097Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3097 raw3097Labels = mixedMoment B raw3097step0 raw3097step0Labels := by
      have hz : ∀ j, raw3097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3097step0 = (fun i j => raw3097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3097step0 raw3097; decide +kernel
      have hl : raw3097step0Labels = raw3097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3097 raw3097Labels permutation434 hz
    mixedMoment B raw3097step0 raw3097step0Labels = mixedMoment B raw3097step1 raw3097step1Labels := by
      have hz : ∀ j, raw3097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3097step1 = (fun i j => raw3097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3097step1 raw3097step0; decide +kernel
      have hl : raw3097step1Labels = raw3097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3097step0 raw3097step0Labels permutation80 hz
    mixedMoment B raw3097step1 raw3097step1Labels = mixedMoment B raw3097step2 raw3097step2Labels := by
      have ha : raw3097step2 = (fun i j => raw3097step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3097step2 raw3097step1; decide +kernel
      have hl : raw3097step2Labels = raw3097step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3097step1 raw3097step1Labels permutation10 permutation3
    mixedMoment B raw3097step2 raw3097step2Labels = mixedMoment B raw3097step3 raw3097step3Labels := by
      have ha : raw3097step3 = raw3097step2 := by apply Matrix.ext; unfold raw3097step3 raw3097step2; decide +kernel
      have hl : raw3097step2Labels = labelEmbedding6 ∘ raw3097step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3097step2 raw3097step2Labels raw3097step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw3098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3098step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3098step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3098 raw3098Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw3098 raw3098Labels = mixedMoment B raw3098step0 raw3098step0Labels := by
      have hz : ∀ j, raw3098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3098step0 = (fun i j => raw3098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3098step0 raw3098; decide +kernel
      have hl : raw3098step0Labels = raw3098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3098 raw3098Labels permutation434 hz
    mixedMoment B raw3098step0 raw3098step0Labels = mixedMoment B raw3098step1 raw3098step1Labels := by
      have hz : ∀ j, raw3098step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3098step1 = (fun i j => raw3098step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3098step1 raw3098step0; decide +kernel
      have hl : raw3098step1Labels = raw3098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3098step0 raw3098step0Labels permutation80 hz
    mixedMoment B raw3098step1 raw3098step1Labels = mixedMoment B raw3098step2 raw3098step2Labels := by
      have ha : raw3098step2 = (fun i j => raw3098step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3098step2 raw3098step1; decide +kernel
      have hl : raw3098step2Labels = raw3098step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3098step1 raw3098step1Labels permutation12 permutation2
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw3099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3099step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3099step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3099 raw3099Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw3099 raw3099Labels = mixedMoment B raw3099step0 raw3099step0Labels := by
      have hz : ∀ j, raw3099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3099step0 = (fun i j => raw3099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3099step0 raw3099; decide +kernel
      have hl : raw3099step0Labels = raw3099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3099 raw3099Labels permutation434 hz
    mixedMoment B raw3099step0 raw3099step0Labels = mixedMoment B raw3099step1 raw3099step1Labels := by
      have ha : raw3099step1 = (fun i j => raw3099step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3099step1 raw3099step0; decide +kernel
      have hl : raw3099step1Labels = raw3099step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3099step0 raw3099step0Labels permutation34 permutation3
    mixedMoment B raw3099step1 raw3099step1Labels = mixedMoment B raw3099step2 raw3099step2Labels := by
      have ha : raw3099step2 = raw3099step1 := by apply Matrix.ext; unfold raw3099step2 raw3099step1; decide +kernel
      have hl : raw3099step1Labels = labelEmbedding6 ∘ raw3099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3099step1 raw3099step1Labels raw3099step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw3100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3100step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3100step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3100step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3100step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3100 raw3100Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw3100 raw3100Labels = mixedMoment B raw3100step0 raw3100step0Labels := by
      have hz : ∀ j, raw3100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3100step0 = (fun i j => raw3100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3100step0 raw3100; decide +kernel
      have hl : raw3100step0Labels = raw3100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3100 raw3100Labels permutation434 hz
    mixedMoment B raw3100step0 raw3100step0Labels = mixedMoment B raw3100step1 raw3100step1Labels := by
      have ha : raw3100step1 = (fun i j => raw3100step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3100step1 raw3100step0; decide +kernel
      have hl : raw3100step1Labels = raw3100step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3100step0 raw3100step0Labels permutation58 permutation5
    mixedMoment B raw3100step1 raw3100step1Labels = mixedMoment B raw3100step2 raw3100step2Labels := by
      have ha : raw3100step2 = -raw3100step1 := by apply Matrix.ext; change ∀ i j, raw3100step2 i j = -(raw3100step1 i j); unfold raw3100step2 raw3100step1; decide +kernel
      have hl : raw3100step2Labels = raw3100step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3100step2 raw3100step2Labels = mixedMoment B raw3100step3 raw3100step3Labels := by
      have ha : raw3100step3 = raw3100step2 := by apply Matrix.ext; unfold raw3100step3 raw3100step2; decide +kernel
      have hl : raw3100step2Labels = labelEmbedding8 ∘ raw3100step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3100step2 raw3100step2Labels raw3100step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw3101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3101step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3101 raw3101Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw3101 raw3101Labels = mixedMoment B raw3101step0 raw3101step0Labels := by
      have ha : raw3101step0 = (fun i j => raw3101 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3101step0 raw3101; decide +kernel
      have hl : raw3101step0Labels = raw3101Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3101 raw3101Labels permutation202 permutation3
    mixedMoment B raw3101step0 raw3101step0Labels = mixedMoment B raw3101step1 raw3101step1Labels := by
      have ha : raw3101step1 = raw3101step0 := by apply Matrix.ext; unfold raw3101step1 raw3101step0; decide +kernel
      have hl : raw3101step0Labels = labelEmbedding6 ∘ raw3101step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3101step0 raw3101step0Labels raw3101step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw3102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3102step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3102 raw3102Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3102 raw3102Labels = mixedMoment B raw3102step0 raw3102step0Labels := by
      have hz : ∀ j, raw3102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3102step0 = (fun i j => raw3102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3102step0 raw3102; decide +kernel
      have hl : raw3102step0Labels = raw3102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3102 raw3102Labels permutation434 hz
    mixedMoment B raw3102step0 raw3102step0Labels = mixedMoment B raw3102step1 raw3102step1Labels := by
      have ha : raw3102step1 = (fun i j => raw3102step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3102step1 raw3102step0; decide +kernel
      have hl : raw3102step1Labels = raw3102step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3102step0 raw3102step0Labels permutation143 permutation5
    mixedMoment B raw3102step1 raw3102step1Labels = mixedMoment B raw3102step2 raw3102step2Labels := by
      have ha : raw3102step2 = raw3102step1 := by apply Matrix.ext; unfold raw3102step2 raw3102step1; decide +kernel
      have hl : raw3102step1Labels = labelEmbedding8 ∘ raw3102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3102step1 raw3102step1Labels raw3102step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3103 raw3103Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3103 raw3103Labels = mixedMoment B raw3103step0 raw3103step0Labels := by
      have hz : ∀ j, raw3103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3103step0 = (fun i j => raw3103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3103step0 raw3103; decide +kernel
      have hl : raw3103step0Labels = raw3103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3103 raw3103Labels permutation434 hz
    mixedMoment B raw3103step0 raw3103step0Labels = mixedMoment B raw3103step1 raw3103step1Labels := by
      have ha : raw3103step1 = (fun i j => raw3103step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3103step1 raw3103step0; decide +kernel
      have hl : raw3103step1Labels = raw3103step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3103step0 raw3103step0Labels permutation50 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3104step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3104 raw3104Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw3104 raw3104Labels = mixedMoment B raw3104step0 raw3104step0Labels := by
      have hz : ∀ j, raw3104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3104step0 = (fun i j => raw3104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3104step0 raw3104; decide +kernel
      have hl : raw3104step0Labels = raw3104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3104 raw3104Labels permutation346 hz
    mixedMoment B raw3104step0 raw3104step0Labels = mixedMoment B raw3104step1 raw3104step1Labels := by
      have ha : raw3104step1 = (fun i j => raw3104step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3104step1 raw3104step0; decide +kernel
      have hl : raw3104step1Labels = raw3104step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3104step0 raw3104step0Labels permutation34 permutation3
    mixedMoment B raw3104step1 raw3104step1Labels = mixedMoment B raw3104step2 raw3104step2Labels := by
      have ha : raw3104step2 = raw3104step1 := by apply Matrix.ext; unfold raw3104step2 raw3104step1; decide +kernel
      have hl : raw3104step1Labels = labelEmbedding6 ∘ raw3104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3104step1 raw3104step1Labels raw3104step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw3105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3105step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3105step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3105step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3105step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3105 raw3105Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw3105 raw3105Labels = mixedMoment B raw3105step0 raw3105step0Labels := by
      have hz : ∀ j, raw3105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3105step0 = (fun i j => raw3105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3105step0 raw3105; decide +kernel
      have hl : raw3105step0Labels = raw3105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3105 raw3105Labels permutation346 hz
    mixedMoment B raw3105step0 raw3105step0Labels = mixedMoment B raw3105step1 raw3105step1Labels := by
      have ha : raw3105step1 = (fun i j => raw3105step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3105step1 raw3105step0; decide +kernel
      have hl : raw3105step1Labels = raw3105step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3105step0 raw3105step0Labels permutation58 permutation5
    mixedMoment B raw3105step1 raw3105step1Labels = mixedMoment B raw3105step2 raw3105step2Labels := by
      have ha : raw3105step2 = -raw3105step1 := by apply Matrix.ext; change ∀ i j, raw3105step2 i j = -(raw3105step1 i j); unfold raw3105step2 raw3105step1; decide +kernel
      have hl : raw3105step2Labels = raw3105step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3105step2 raw3105step2Labels = mixedMoment B raw3105step3 raw3105step3Labels := by
      have ha : raw3105step3 = raw3105step2 := by apply Matrix.ext; unfold raw3105step3 raw3105step2; decide +kernel
      have hl : raw3105step2Labels = labelEmbedding8 ∘ raw3105step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3105step2 raw3105step2Labels raw3105step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw3106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1]]
def raw3106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3106step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3106 raw3106Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw3106 raw3106Labels = mixedMoment B raw3106step0 raw3106step0Labels := by
      have ha : raw3106step0 = (fun i j => raw3106 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3106step0 raw3106; decide +kernel
      have hl : raw3106step0Labels = raw3106Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3106 raw3106Labels permutation178 permutation3
    mixedMoment B raw3106step0 raw3106step0Labels = mixedMoment B raw3106step1 raw3106step1Labels := by
      have ha : raw3106step1 = raw3106step0 := by apply Matrix.ext; unfold raw3106step1 raw3106step0; decide +kernel
      have hl : raw3106step0Labels = labelEmbedding6 ∘ raw3106step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3106step0 raw3106step0Labels raw3106step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw3107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1]]
def raw3107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3107step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3107 raw3107Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3107 raw3107Labels = mixedMoment B raw3107step0 raw3107step0Labels := by
      have hz : ∀ j, raw3107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3107step0 = (fun i j => raw3107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3107step0 raw3107; decide +kernel
      have hl : raw3107step0Labels = raw3107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3107 raw3107Labels permutation346 hz
    mixedMoment B raw3107step0 raw3107step0Labels = mixedMoment B raw3107step1 raw3107step1Labels := by
      have ha : raw3107step1 = (fun i j => raw3107step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3107step1 raw3107step0; decide +kernel
      have hl : raw3107step1Labels = raw3107step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3107step0 raw3107step0Labels permutation143 permutation5
    mixedMoment B raw3107step1 raw3107step1Labels = mixedMoment B raw3107step2 raw3107step2Labels := by
      have ha : raw3107step2 = raw3107step1 := by apply Matrix.ext; unfold raw3107step2 raw3107step1; decide +kernel
      have hl : raw3107step1Labels = labelEmbedding8 ∘ raw3107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3107step1 raw3107step1Labels raw3107step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1]]
def raw3108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3108 raw3108Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3108 raw3108Labels = mixedMoment B raw3108step0 raw3108step0Labels := by
      have hz : ∀ j, raw3108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3108step0 = (fun i j => raw3108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3108step0 raw3108; decide +kernel
      have hl : raw3108step0Labels = raw3108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3108 raw3108Labels permutation346 hz
    mixedMoment B raw3108step0 raw3108step0Labels = mixedMoment B raw3108step1 raw3108step1Labels := by
      have ha : raw3108step1 = (fun i j => raw3108step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3108step1 raw3108step0; decide +kernel
      have hl : raw3108step1Labels = raw3108step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3108step0 raw3108step0Labels permutation50 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw3109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3109step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3109step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3109step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3109 raw3109Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw3109 raw3109Labels = mixedMoment B raw3109step0 raw3109step0Labels := by
      have hz : ∀ j, raw3109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3109step0 = (fun i j => raw3109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3109step0 raw3109; decide +kernel
      have hl : raw3109step0Labels = raw3109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3109 raw3109Labels permutation434 hz
    mixedMoment B raw3109step0 raw3109step0Labels = mixedMoment B raw3109step1 raw3109step1Labels := by
      have hz : ∀ j, raw3109step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3109step1 = (fun i j => raw3109step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3109step1 raw3109step0; decide +kernel
      have hl : raw3109step1Labels = raw3109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3109step0 raw3109step0Labels permutation80 hz
    mixedMoment B raw3109step1 raw3109step1Labels = mixedMoment B raw3109step2 raw3109step2Labels := by
      have ha : raw3109step2 = (fun i j => raw3109step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3109step2 raw3109step1; decide +kernel
      have hl : raw3109step2Labels = raw3109step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3109step1 raw3109step1Labels permutation9 permutation3
    mixedMoment B raw3109step2 raw3109step2Labels = mixedMoment B raw3109step3 raw3109step3Labels := by
      have ha : raw3109step3 = raw3109step2 := by apply Matrix.ext; unfold raw3109step3 raw3109step2; decide +kernel
      have hl : raw3109step2Labels = labelEmbedding6 ∘ raw3109step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3109step2 raw3109step2Labels raw3109step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw3110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![2, -1, -1], ![1, -2, 1]]
def raw3110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw3110step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3110step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw3110step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3110 raw3110Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw3110 raw3110Labels = mixedMoment B raw3110step0 raw3110step0Labels := by
      have hz : ∀ j, raw3110 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3110step0 = (fun i j => raw3110 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3110step0 raw3110; decide +kernel
      have hl : raw3110step0Labels = raw3110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3110 raw3110Labels permutation434 hz
    mixedMoment B raw3110step0 raw3110step0Labels = mixedMoment B raw3110step1 raw3110step1Labels := by
      have hz : ∀ j, raw3110step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3110step1 = (fun i j => raw3110step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3110step1 raw3110step0; decide +kernel
      have hl : raw3110step1Labels = raw3110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3110step0 raw3110step0Labels permutation80 hz
    mixedMoment B raw3110step1 raw3110step1Labels = mixedMoment B raw3110step2 raw3110step2Labels := by
      have ha : raw3110step2 = (fun i j => raw3110step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3110step2 raw3110step1; decide +kernel
      have hl : raw3110step2Labels = raw3110step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3110step1 raw3110step1Labels permutation9 permutation3
    mixedMoment B raw3110step2 raw3110step2Labels = mixedMoment B raw3110step3 raw3110step3Labels := by
      have ha : raw3110step3 = raw3110step2 := by apply Matrix.ext; unfold raw3110step3 raw3110step2; decide +kernel
      have hl : raw3110step2Labels = labelEmbedding6 ∘ raw3110step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3110step2 raw3110step2Labels raw3110step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

def raw3111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3111step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3111step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3111step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3111step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3111 raw3111Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw3111 raw3111Labels = mixedMoment B raw3111step0 raw3111step0Labels := by
      have hz : ∀ j, raw3111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3111step0 = (fun i j => raw3111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3111step0 raw3111; decide +kernel
      have hl : raw3111step0Labels = raw3111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3111 raw3111Labels permutation434 hz
    mixedMoment B raw3111step0 raw3111step0Labels = mixedMoment B raw3111step1 raw3111step1Labels := by
      have ha : raw3111step1 = (fun i j => raw3111step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3111step1 raw3111step0; decide +kernel
      have hl : raw3111step1Labels = raw3111step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3111step0 raw3111step0Labels permutation125 permutation3
    mixedMoment B raw3111step1 raw3111step1Labels = mixedMoment B raw3111step2 raw3111step2Labels := by
      have ha : raw3111step2 = -raw3111step1 := by apply Matrix.ext; change ∀ i j, raw3111step2 i j = -(raw3111step1 i j); unfold raw3111step2 raw3111step1; decide +kernel
      have hl : raw3111step2Labels = raw3111step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3111step2 raw3111step2Labels = mixedMoment B raw3111step3 raw3111step3Labels := by
      have ha : raw3111step3 = raw3111step2 := by apply Matrix.ext; unfold raw3111step3 raw3111step2; decide +kernel
      have hl : raw3111step2Labels = labelEmbedding6 ∘ raw3111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3111step2 raw3111step2Labels raw3111step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw3112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1]]
def raw3112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3112step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3112step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3112step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3112step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3112 raw3112Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw3112 raw3112Labels = mixedMoment B raw3112step0 raw3112step0Labels := by
      have hz : ∀ j, raw3112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3112step0 = (fun i j => raw3112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3112step0 raw3112; decide +kernel
      have hl : raw3112step0Labels = raw3112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3112 raw3112Labels permutation346 hz
    mixedMoment B raw3112step0 raw3112step0Labels = mixedMoment B raw3112step1 raw3112step1Labels := by
      have ha : raw3112step1 = (fun i j => raw3112step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3112step1 raw3112step0; decide +kernel
      have hl : raw3112step1Labels = raw3112step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3112step0 raw3112step0Labels permutation125 permutation3
    mixedMoment B raw3112step1 raw3112step1Labels = mixedMoment B raw3112step2 raw3112step2Labels := by
      have ha : raw3112step2 = -raw3112step1 := by apply Matrix.ext; change ∀ i j, raw3112step2 i j = -(raw3112step1 i j); unfold raw3112step2 raw3112step1; decide +kernel
      have hl : raw3112step2Labels = raw3112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3112step2 raw3112step2Labels = mixedMoment B raw3112step3 raw3112step3Labels := by
      have ha : raw3112step3 = raw3112step2 := by apply Matrix.ext; unfold raw3112step3 raw3112step2; decide +kernel
      have hl : raw3112step2Labels = labelEmbedding6 ∘ raw3112step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3112step2 raw3112step2Labels raw3112step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw3113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1]]
def raw3113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1]]
def raw3113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![0, -1, 1]]
def raw3113step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3113step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3113 raw3113Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw3113 raw3113Labels = mixedMoment B raw3113step0 raw3113step0Labels := by
      have hz : ∀ j, raw3113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3113step0 = (fun i j => raw3113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3113step0 raw3113; decide +kernel
      have hl : raw3113step0Labels = raw3113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3113 raw3113Labels permutation434 hz
    mixedMoment B raw3113step0 raw3113step0Labels = mixedMoment B raw3113step1 raw3113step1Labels := by
      have hz : ∀ j, raw3113step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3113step1 = (fun i j => raw3113step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3113step1 raw3113step0; decide +kernel
      have hl : raw3113step1Labels = raw3113step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3113step0 raw3113step0Labels permutation80 hz
    mixedMoment B raw3113step1 raw3113step1Labels = mixedMoment B raw3113step2 raw3113step2Labels := by
      have ha : raw3113step2 = (fun i j => raw3113step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3113step2 raw3113step1; decide +kernel
      have hl : raw3113step2Labels = raw3113step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3113step1 raw3113step1Labels permutation12 permutation2
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw3114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw3114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw3114step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3114step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw3114step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3114 raw3114Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw3114 raw3114Labels = mixedMoment B raw3114step0 raw3114step0Labels := by
      have hz : ∀ j, raw3114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3114step0 = (fun i j => raw3114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3114step0 raw3114; decide +kernel
      have hl : raw3114step0Labels = raw3114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3114 raw3114Labels permutation434 hz
    mixedMoment B raw3114step0 raw3114step0Labels = mixedMoment B raw3114step1 raw3114step1Labels := by
      have hz : ∀ j, raw3114step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3114step1 = (fun i j => raw3114step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3114step1 raw3114step0; decide +kernel
      have hl : raw3114step1Labels = raw3114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3114step0 raw3114step0Labels permutation80 hz
    mixedMoment B raw3114step1 raw3114step1Labels = mixedMoment B raw3114step2 raw3114step2Labels := by
      have ha : raw3114step2 = (fun i j => raw3114step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3114step2 raw3114step1; decide +kernel
      have hl : raw3114step2Labels = raw3114step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3114step1 raw3114step1Labels permutation8 permutation3
    mixedMoment B raw3114step2 raw3114step2Labels = mixedMoment B raw3114step3 raw3114step3Labels := by
      have ha : raw3114step3 = raw3114step2 := by apply Matrix.ext; unfold raw3114step3 raw3114step2; decide +kernel
      have hl : raw3114step2Labels = labelEmbedding6 ∘ raw3114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3114step2 raw3114step2Labels raw3114step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw3115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw3115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3115step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3115step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3115step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3115 raw3115Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw3115 raw3115Labels = mixedMoment B raw3115step0 raw3115step0Labels := by
      have hz : ∀ j, raw3115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3115step0 = (fun i j => raw3115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3115step0 raw3115; decide +kernel
      have hl : raw3115step0Labels = raw3115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3115 raw3115Labels permutation434 hz
    mixedMoment B raw3115step0 raw3115step0Labels = mixedMoment B raw3115step1 raw3115step1Labels := by
      have hz : ∀ j, raw3115step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3115step1 = (fun i j => raw3115step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3115step1 raw3115step0; decide +kernel
      have hl : raw3115step1Labels = raw3115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3115step0 raw3115step0Labels permutation80 hz
    mixedMoment B raw3115step1 raw3115step1Labels = mixedMoment B raw3115step2 raw3115step2Labels := by
      have ha : raw3115step2 = (fun i j => raw3115step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3115step2 raw3115step1; decide +kernel
      have hl : raw3115step2Labels = raw3115step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3115step1 raw3115step1Labels permutation30 permutation5
    mixedMoment B raw3115step2 raw3115step2Labels = mixedMoment B raw3115step3 raw3115step3Labels := by
      have ha : raw3115step3 = raw3115step2 := by apply Matrix.ext; unfold raw3115step3 raw3115step2; decide +kernel
      have hl : raw3115step2Labels = labelEmbedding8 ∘ raw3115step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3115step2 raw3115step2Labels raw3115step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw3116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3116step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3116step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3116 raw3116Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw3116 raw3116Labels = mixedMoment B raw3116step0 raw3116step0Labels := by
      have hz : ∀ j, raw3116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3116step0 = (fun i j => raw3116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3116step0 raw3116; decide +kernel
      have hl : raw3116step0Labels = raw3116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3116 raw3116Labels permutation434 hz
    mixedMoment B raw3116step0 raw3116step0Labels = mixedMoment B raw3116step1 raw3116step1Labels := by
      have ha : raw3116step1 = (fun i j => raw3116step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3116step1 raw3116step0; decide +kernel
      have hl : raw3116step1Labels = raw3116step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3116step0 raw3116step0Labels permutation149 permutation5
    mixedMoment B raw3116step1 raw3116step1Labels = mixedMoment B raw3116step2 raw3116step2Labels := by
      have ha : raw3116step2 = raw3116step1 := by apply Matrix.ext; unfold raw3116step2 raw3116step1; decide +kernel
      have hl : raw3116step1Labels = labelEmbedding8 ∘ raw3116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3116step1 raw3116step1Labels raw3116step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw3117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw3117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3117step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3117step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3117 raw3117Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw3117 raw3117Labels = mixedMoment B raw3117step0 raw3117step0Labels := by
      have hz : ∀ j, raw3117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3117step0 = (fun i j => raw3117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3117step0 raw3117; decide +kernel
      have hl : raw3117step0Labels = raw3117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3117 raw3117Labels permutation346 hz
    mixedMoment B raw3117step0 raw3117step0Labels = mixedMoment B raw3117step1 raw3117step1Labels := by
      have ha : raw3117step1 = (fun i j => raw3117step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3117step1 raw3117step0; decide +kernel
      have hl : raw3117step1Labels = raw3117step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3117step0 raw3117step0Labels permutation149 permutation5
    mixedMoment B raw3117step1 raw3117step1Labels = mixedMoment B raw3117step2 raw3117step2Labels := by
      have ha : raw3117step2 = raw3117step1 := by apply Matrix.ext; unfold raw3117step2 raw3117step1; decide +kernel
      have hl : raw3117step1Labels = labelEmbedding8 ∘ raw3117step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3117step1 raw3117step1Labels raw3117step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw3118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1]]
def raw3118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1]]
def raw3118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw3118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3118step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3118step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3118step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3118 raw3118Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw3118 raw3118Labels = mixedMoment B raw3118step0 raw3118step0Labels := by
      have hz : ∀ j, raw3118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3118step0 = (fun i j => raw3118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3118step0 raw3118; decide +kernel
      have hl : raw3118step0Labels = raw3118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3118 raw3118Labels permutation434 hz
    mixedMoment B raw3118step0 raw3118step0Labels = mixedMoment B raw3118step1 raw3118step1Labels := by
      have hz : ∀ j, raw3118step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3118step1 = (fun i j => raw3118step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3118step1 raw3118step0; decide +kernel
      have hl : raw3118step1Labels = raw3118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3118step0 raw3118step0Labels permutation80 hz
    mixedMoment B raw3118step1 raw3118step1Labels = mixedMoment B raw3118step2 raw3118step2Labels := by
      have ha : raw3118step2 = (fun i j => raw3118step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3118step2 raw3118step1; decide +kernel
      have hl : raw3118step2Labels = raw3118step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3118step1 raw3118step1Labels permutation29 permutation5
    mixedMoment B raw3118step2 raw3118step2Labels = mixedMoment B raw3118step3 raw3118step3Labels := by
      have ha : raw3118step3 = raw3118step2 := by apply Matrix.ext; unfold raw3118step3 raw3118step2; decide +kernel
      have hl : raw3118step2Labels = labelEmbedding8 ∘ raw3118step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3118step2 raw3118step2Labels raw3118step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw3119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3119 raw3119Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3119 raw3119Labels = mixedMoment B raw3119step0 raw3119step0Labels := by
      have hz : ∀ j, raw3119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3119step0 = (fun i j => raw3119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3119step0 raw3119; decide +kernel
      have hl : raw3119step0Labels = raw3119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3119 raw3119Labels permutation346 hz
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3120 raw3120Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw3120 raw3120Labels = mixedMoment B raw3120step0 raw3120step0Labels := by
      have ha : raw3120step0 = (fun i j => raw3120 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3120step0 raw3120; decide +kernel
      have hl : raw3120step0Labels = raw3120Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3120 raw3120Labels permutation176 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

def raw3121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3121step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3121step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3121step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3121step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3121 raw3121Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3121 raw3121Labels = mixedMoment B raw3121step0 raw3121step0Labels := by
      have hz : ∀ j, raw3121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3121step0 = (fun i j => raw3121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3121step0 raw3121; decide +kernel
      have hl : raw3121step0Labels = raw3121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3121 raw3121Labels permutation346 hz
    mixedMoment B raw3121step0 raw3121step0Labels = mixedMoment B raw3121step1 raw3121step1Labels := by
      have ha : raw3121step1 = (fun i j => raw3121step0 (permutation99 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3121step1 raw3121step0; decide +kernel
      have hl : raw3121step1Labels = raw3121step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3121step0 raw3121step0Labels permutation99 permutation4
    mixedMoment B raw3121step1 raw3121step1Labels = mixedMoment B raw3121step2 raw3121step2Labels := by
      have ha : raw3121step2 = -raw3121step1 := by apply Matrix.ext; change ∀ i j, raw3121step2 i j = -(raw3121step1 i j); unfold raw3121step2 raw3121step1; decide +kernel
      have hl : raw3121step2Labels = raw3121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3121step2 raw3121step2Labels = mixedMoment B raw3121step3 raw3121step3Labels := by
      have ha : raw3121step3 = raw3121step2 := by apply Matrix.ext; unfold raw3121step3 raw3121step2; decide +kernel
      have hl : raw3121step2Labels = labelEmbedding7 ∘ raw3121step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3121step2 raw3121step2Labels raw3121step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3122step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3122step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3122step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3122step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3122 raw3122Labels = mixedMoment B node5501 node5501Labels := by
  calc
    mixedMoment B raw3122 raw3122Labels = mixedMoment B raw3122step0 raw3122step0Labels := by
      have hz : ∀ j, raw3122 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3122step0 = (fun i j => raw3122 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3122step0 raw3122; decide +kernel
      have hl : raw3122step0Labels = raw3122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3122 raw3122Labels permutation520 hz
    mixedMoment B raw3122step0 raw3122step0Labels = mixedMoment B raw3122step1 raw3122step1Labels := by
      have hz : ∀ j, raw3122step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3122step1 = (fun i j => raw3122step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3122step1 raw3122step0; decide +kernel
      have hl : raw3122step1Labels = raw3122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3122step0 raw3122step0Labels permutation80 hz
    mixedMoment B raw3122step1 raw3122step1Labels = mixedMoment B raw3122step2 raw3122step2Labels := by
      have ha : raw3122step2 = (fun i j => raw3122step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3122step2 raw3122step1; decide +kernel
      have hl : raw3122step2Labels = raw3122step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3122step1 raw3122step1Labels permutation24 permutation6
    mixedMoment B raw3122step2 raw3122step2Labels = mixedMoment B raw3122step3 raw3122step3Labels := by
      have ha : raw3122step3 = raw3122step2 := by apply Matrix.ext; unfold raw3122step3 raw3122step2; decide +kernel
      have hl : raw3122step2Labels = labelEmbedding9 ∘ raw3122step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3122step2 raw3122step2Labels raw3122step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5501 node5501Labels := by rfl

def raw3123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3123step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3123step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3123step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3123step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3123 raw3123Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3123 raw3123Labels = mixedMoment B raw3123step0 raw3123step0Labels := by
      have hz : ∀ j, raw3123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3123step0 = (fun i j => raw3123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3123step0 raw3123; decide +kernel
      have hl : raw3123step0Labels = raw3123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3123 raw3123Labels permutation346 hz
    mixedMoment B raw3123step0 raw3123step0Labels = mixedMoment B raw3123step1 raw3123step1Labels := by
      have ha : raw3123step1 = (fun i j => raw3123step0 (permutation99 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3123step1 raw3123step0; decide +kernel
      have hl : raw3123step1Labels = raw3123step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3123step0 raw3123step0Labels permutation99 permutation4
    mixedMoment B raw3123step1 raw3123step1Labels = mixedMoment B raw3123step2 raw3123step2Labels := by
      have ha : raw3123step2 = -raw3123step1 := by apply Matrix.ext; change ∀ i j, raw3123step2 i j = -(raw3123step1 i j); unfold raw3123step2 raw3123step1; decide +kernel
      have hl : raw3123step2Labels = raw3123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3123step2 raw3123step2Labels = mixedMoment B raw3123step3 raw3123step3Labels := by
      have ha : raw3123step3 = raw3123step2 := by apply Matrix.ext; unfold raw3123step3 raw3123step2; decide +kernel
      have hl : raw3123step2Labels = labelEmbedding7 ∘ raw3123step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3123step2 raw3123step2Labels raw3123step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3124 raw3124Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw3124 raw3124Labels = mixedMoment B raw3124step0 raw3124step0Labels := by
      have hz : ∀ j, raw3124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3124step0 = (fun i j => raw3124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3124step0 raw3124; decide +kernel
      have hl : raw3124step0Labels = raw3124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3124 raw3124Labels permutation346 hz
    mixedMoment B raw3124step0 raw3124step0Labels = mixedMoment B raw3124step1 raw3124step1Labels := by
      have ha : raw3124step1 = (fun i j => raw3124step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3124step1 raw3124step0; decide +kernel
      have hl : raw3124step1Labels = raw3124step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3124step0 raw3124step0Labels permutation43 permutation3
    mixedMoment B raw3124step1 raw3124step1Labels = mixedMoment B raw3124step2 raw3124step2Labels := by
      have ha : raw3124step2 = raw3124step1 := by apply Matrix.ext; unfold raw3124step2 raw3124step1; decide +kernel
      have hl : raw3124step1Labels = labelEmbedding6 ∘ raw3124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3124step1 raw3124step1Labels raw3124step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw3125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3125step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3125 raw3125Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw3125 raw3125Labels = mixedMoment B raw3125step0 raw3125step0Labels := by
      have ha : raw3125step0 = (fun i j => raw3125 (permutation187 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3125step0 raw3125; decide +kernel
      have hl : raw3125step0Labels = raw3125Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3125 raw3125Labels permutation187 permutation3
    mixedMoment B raw3125step0 raw3125step0Labels = mixedMoment B raw3125step1 raw3125step1Labels := by
      have ha : raw3125step1 = raw3125step0 := by apply Matrix.ext; unfold raw3125step1 raw3125step0; decide +kernel
      have hl : raw3125step0Labels = labelEmbedding6 ∘ raw3125step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3125step0 raw3125step0Labels raw3125step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw3126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3126step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3126step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3126step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3126 raw3126Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw3126 raw3126Labels = mixedMoment B raw3126step0 raw3126step0Labels := by
      have hz : ∀ j, raw3126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3126step0 = (fun i j => raw3126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3126step0 raw3126; decide +kernel
      have hl : raw3126step0Labels = raw3126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3126 raw3126Labels permutation346 hz
    mixedMoment B raw3126step0 raw3126step0Labels = mixedMoment B raw3126step1 raw3126step1Labels := by
      have ha : raw3126step1 = (fun i j => raw3126step0 (permutation85 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3126step1 raw3126step0; decide +kernel
      have hl : raw3126step1Labels = raw3126step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3126step0 raw3126step0Labels permutation85 permutation5
    mixedMoment B raw3126step1 raw3126step1Labels = mixedMoment B raw3126step2 raw3126step2Labels := by
      have ha : raw3126step2 = -raw3126step1 := by apply Matrix.ext; change ∀ i j, raw3126step2 i j = -(raw3126step1 i j); unfold raw3126step2 raw3126step1; decide +kernel
      have hl : raw3126step2Labels = raw3126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3126step2 raw3126step2Labels = mixedMoment B raw3126step3 raw3126step3Labels := by
      have ha : raw3126step3 = raw3126step2 := by apply Matrix.ext; unfold raw3126step3 raw3126step2; decide +kernel
      have hl : raw3126step2Labels = labelEmbedding8 ∘ raw3126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3126step2 raw3126step2Labels raw3126step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw3127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3127step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3127step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3127step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3127 raw3127Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3127 raw3127Labels = mixedMoment B raw3127step0 raw3127step0Labels := by
      have hz : ∀ j, raw3127 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3127step0 = (fun i j => raw3127 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3127step0 raw3127; decide +kernel
      have hl : raw3127step0Labels = raw3127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3127 raw3127Labels permutation520 hz
    mixedMoment B raw3127step0 raw3127step0Labels = mixedMoment B raw3127step1 raw3127step1Labels := by
      have hz : ∀ j, raw3127step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3127step1 = (fun i j => raw3127step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3127step1 raw3127step0; decide +kernel
      have hl : raw3127step1Labels = raw3127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3127step0 raw3127step0Labels permutation80 hz
    mixedMoment B raw3127step1 raw3127step1Labels = mixedMoment B raw3127step2 raw3127step2Labels := by
      have ha : raw3127step2 = (fun i j => raw3127step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3127step2 raw3127step1; decide +kernel
      have hl : raw3127step2Labels = raw3127step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3127step1 raw3127step1Labels permutation11 permutation3
    mixedMoment B raw3127step2 raw3127step2Labels = mixedMoment B raw3127step3 raw3127step3Labels := by
      have ha : raw3127step3 = raw3127step2 := by apply Matrix.ext; unfold raw3127step3 raw3127step2; decide +kernel
      have hl : raw3127step2Labels = labelEmbedding6 ∘ raw3127step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3127step2 raw3127step2Labels raw3127step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3128step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3128step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3128 raw3128Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3128 raw3128Labels = mixedMoment B raw3128step0 raw3128step0Labels := by
      have hz : ∀ j, raw3128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3128step0 = (fun i j => raw3128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3128step0 raw3128; decide +kernel
      have hl : raw3128step0Labels = raw3128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3128 raw3128Labels permutation346 hz
    mixedMoment B raw3128step0 raw3128step0Labels = mixedMoment B raw3128step1 raw3128step1Labels := by
      have ha : raw3128step1 = (fun i j => raw3128step0 (permutation71 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3128step1 raw3128step0; decide +kernel
      have hl : raw3128step1Labels = raw3128step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3128step0 raw3128step0Labels permutation71 permutation5
    mixedMoment B raw3128step1 raw3128step1Labels = mixedMoment B raw3128step2 raw3128step2Labels := by
      have ha : raw3128step2 = raw3128step1 := by apply Matrix.ext; unfold raw3128step2 raw3128step1; decide +kernel
      have hl : raw3128step1Labels = labelEmbedding8 ∘ raw3128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3128step1 raw3128step1Labels raw3128step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3129step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3129step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3129 raw3129Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw3129 raw3129Labels = mixedMoment B raw3129step0 raw3129step0Labels := by
      have ha : raw3129step0 = (fun i j => raw3129 (permutation204 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3129step0 raw3129; decide +kernel
      have hl : raw3129step0Labels = raw3129Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3129 raw3129Labels permutation204 permutation3
    mixedMoment B raw3129step0 raw3129step0Labels = mixedMoment B raw3129step1 raw3129step1Labels := by
      have ha : raw3129step1 = raw3129step0 := by apply Matrix.ext; unfold raw3129step1 raw3129step0; decide +kernel
      have hl : raw3129step0Labels = labelEmbedding6 ∘ raw3129step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3129step0 raw3129step0Labels raw3129step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw3130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3130 raw3130Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3130 raw3130Labels = mixedMoment B raw3130step0 raw3130step0Labels := by
      have ha : raw3130step0 = (fun i j => raw3130 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3130step0 raw3130; decide +kernel
      have hl : raw3130step0Labels = raw3130Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3130 raw3130Labels permutation158 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3131step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3131 raw3131Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw3131 raw3131Labels = mixedMoment B raw3131step0 raw3131step0Labels := by
      have ha : raw3131step0 = (fun i j => raw3131 (permutation204 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3131step0 raw3131; decide +kernel
      have hl : raw3131step0Labels = raw3131Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3131 raw3131Labels permutation204 permutation3
    mixedMoment B raw3131step0 raw3131step0Labels = mixedMoment B raw3131step1 raw3131step1Labels := by
      have ha : raw3131step1 = raw3131step0 := by apply Matrix.ext; unfold raw3131step1 raw3131step0; decide +kernel
      have hl : raw3131step0Labels = labelEmbedding6 ∘ raw3131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3131step0 raw3131step0Labels raw3131step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw3132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3132 raw3132Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3132 raw3132Labels = mixedMoment B raw3132step0 raw3132step0Labels := by
      have hz : ∀ j, raw3132 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3132step0 = (fun i j => raw3132 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3132step0 raw3132; decide +kernel
      have hl : raw3132step0Labels = raw3132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3132 raw3132Labels permutation520 hz
    mixedMoment B raw3132step0 raw3132step0Labels = mixedMoment B raw3132step1 raw3132step1Labels := by
      have ha : raw3132step1 = (fun i j => raw3132step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3132step1 raw3132step0; decide +kernel
      have hl : raw3132step1Labels = raw3132step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3132step0 raw3132step0Labels permutation34 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3133step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3133 raw3133Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3133 raw3133Labels = mixedMoment B raw3133step0 raw3133step0Labels := by
      have ha : raw3133step0 = (fun i j => raw3133 (permutation218 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3133step0 raw3133; decide +kernel
      have hl : raw3133step0Labels = raw3133Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3133 raw3133Labels permutation218 permutation3
    mixedMoment B raw3133step0 raw3133step0Labels = mixedMoment B raw3133step1 raw3133step1Labels := by
      have ha : raw3133step1 = raw3133step0 := by apply Matrix.ext; unfold raw3133step1 raw3133step0; decide +kernel
      have hl : raw3133step0Labels = labelEmbedding6 ∘ raw3133step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3133step0 raw3133step0Labels raw3133step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw3134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3134step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3134 raw3134Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw3134 raw3134Labels = mixedMoment B raw3134step0 raw3134step0Labels := by
      have hz : ∀ j, raw3134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3134step0 = (fun i j => raw3134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3134step0 raw3134; decide +kernel
      have hl : raw3134step0Labels = raw3134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3134 raw3134Labels permutation346 hz
    mixedMoment B raw3134step0 raw3134step0Labels = mixedMoment B raw3134step1 raw3134step1Labels := by
      have ha : raw3134step1 = (fun i j => raw3134step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3134step1 raw3134step0; decide +kernel
      have hl : raw3134step1Labels = raw3134step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3134step0 raw3134step0Labels permutation33 permutation3
    mixedMoment B raw3134step1 raw3134step1Labels = mixedMoment B raw3134step2 raw3134step2Labels := by
      have ha : raw3134step2 = raw3134step1 := by apply Matrix.ext; unfold raw3134step2 raw3134step1; decide +kernel
      have hl : raw3134step1Labels = labelEmbedding6 ∘ raw3134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3134step1 raw3134step1Labels raw3134step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw3135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3135 raw3135Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw3135 raw3135Labels = mixedMoment B raw3135step0 raw3135step0Labels := by
      have hz : ∀ j, raw3135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3135step0 = (fun i j => raw3135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3135step0 raw3135; decide +kernel
      have hl : raw3135step0Labels = raw3135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3135 raw3135Labels permutation346 hz
    mixedMoment B raw3135step0 raw3135step0Labels = mixedMoment B raw3135step1 raw3135step1Labels := by
      have ha : raw3135step1 = (fun i j => raw3135step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3135step1 raw3135step0; decide +kernel
      have hl : raw3135step1Labels = raw3135step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3135step0 raw3135step0Labels permutation34 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw3136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3136 raw3136Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3136 raw3136Labels = mixedMoment B raw3136step0 raw3136step0Labels := by
      have ha : raw3136step0 = (fun i j => raw3136 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3136step0 raw3136; decide +kernel
      have hl : raw3136step0Labels = raw3136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3136 raw3136Labels permutation177 permutation3
    mixedMoment B raw3136step0 raw3136step0Labels = mixedMoment B raw3136step1 raw3136step1Labels := by
      have ha : raw3136step1 = raw3136step0 := by apply Matrix.ext; unfold raw3136step1 raw3136step0; decide +kernel
      have hl : raw3136step0Labels = labelEmbedding6 ∘ raw3136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3136step0 raw3136step0Labels raw3136step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3137 raw3137Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw3137 raw3137Labels = mixedMoment B raw3137step0 raw3137step0Labels := by
      have hz : ∀ j, raw3137 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3137step0 = (fun i j => raw3137 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3137step0 raw3137; decide +kernel
      have hl : raw3137step0Labels = raw3137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3137 raw3137Labels permutation520 hz
    mixedMoment B raw3137step0 raw3137step0Labels = mixedMoment B raw3137step1 raw3137step1Labels := by
      have hz : ∀ j, raw3137step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3137step1 = (fun i j => raw3137step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3137step1 raw3137step0; decide +kernel
      have hl : raw3137step1Labels = raw3137step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3137step0 raw3137step0Labels permutation80 hz
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw3138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3138 raw3138Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3138 raw3138Labels = mixedMoment B raw3138step0 raw3138step0Labels := by
      have hz : ∀ j, raw3138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3138step0 = (fun i j => raw3138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3138step0 raw3138; decide +kernel
      have hl : raw3138step0Labels = raw3138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3138 raw3138Labels permutation346 hz
    mixedMoment B raw3138step0 raw3138step0Labels = mixedMoment B raw3138step1 raw3138step1Labels := by
      have ha : raw3138step1 = (fun i j => raw3138step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3138step1 raw3138step0; decide +kernel
      have hl : raw3138step1Labels = raw3138step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3138step0 raw3138step0Labels permutation37 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3139step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3139 raw3139Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw3139 raw3139Labels = mixedMoment B raw3139step0 raw3139step0Labels := by
      have hz : ∀ j, raw3139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3139step0 = (fun i j => raw3139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3139step0 raw3139; decide +kernel
      have hl : raw3139step0Labels = raw3139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3139 raw3139Labels permutation346 hz
    mixedMoment B raw3139step0 raw3139step0Labels = mixedMoment B raw3139step1 raw3139step1Labels := by
      have ha : raw3139step1 = (fun i j => raw3139step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3139step1 raw3139step0; decide +kernel
      have hl : raw3139step1Labels = raw3139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3139step0 raw3139step0Labels permutation39 permutation3
    mixedMoment B raw3139step1 raw3139step1Labels = mixedMoment B raw3139step2 raw3139step2Labels := by
      have ha : raw3139step2 = raw3139step1 := by apply Matrix.ext; unfold raw3139step2 raw3139step1; decide +kernel
      have hl : raw3139step1Labels = labelEmbedding6 ∘ raw3139step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3139step1 raw3139step1Labels raw3139step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw3140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3140step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3140step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3140step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3140 raw3140Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3140 raw3140Labels = mixedMoment B raw3140step0 raw3140step0Labels := by
      have hz : ∀ j, raw3140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3140step0 = (fun i j => raw3140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3140step0 raw3140; decide +kernel
      have hl : raw3140step0Labels = raw3140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3140 raw3140Labels permutation346 hz
    mixedMoment B raw3140step0 raw3140step0Labels = mixedMoment B raw3140step1 raw3140step1Labels := by
      have ha : raw3140step1 = (fun i j => raw3140step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3140step1 raw3140step0; decide +kernel
      have hl : raw3140step1Labels = raw3140step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3140step0 raw3140step0Labels permutation127 permutation3
    mixedMoment B raw3140step1 raw3140step1Labels = mixedMoment B raw3140step2 raw3140step2Labels := by
      have ha : raw3140step2 = -raw3140step1 := by apply Matrix.ext; change ∀ i j, raw3140step2 i j = -(raw3140step1 i j); unfold raw3140step2 raw3140step1; decide +kernel
      have hl : raw3140step2Labels = raw3140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3140step2 raw3140step2Labels = mixedMoment B raw3140step3 raw3140step3Labels := by
      have ha : raw3140step3 = raw3140step2 := by apply Matrix.ext; unfold raw3140step3 raw3140step2; decide +kernel
      have hl : raw3140step2Labels = labelEmbedding6 ∘ raw3140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3140step2 raw3140step2Labels raw3140step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3141 raw3141Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw3141 raw3141Labels = mixedMoment B raw3141step0 raw3141step0Labels := by
      have ha : raw3141step0 = (fun i j => raw3141 (permutation579 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3141step0 raw3141; decide +kernel
      have hl : raw3141step0Labels = raw3141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3141 raw3141Labels permutation579 permutation3
    mixedMoment B raw3141step0 raw3141step0Labels = mixedMoment B raw3141step1 raw3141step1Labels := by
      have ha : raw3141step1 = -raw3141step0 := by apply Matrix.ext; change ∀ i j, raw3141step1 i j = -(raw3141step0 i j); unfold raw3141step1 raw3141step0; decide +kernel
      have hl : raw3141step1Labels = raw3141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3141step1 raw3141step1Labels = mixedMoment B raw3141step2 raw3141step2Labels := by
      have ha : raw3141step2 = raw3141step1 := by apply Matrix.ext; unfold raw3141step2 raw3141step1; decide +kernel
      have hl : raw3141step1Labels = labelEmbedding6 ∘ raw3141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3141step1 raw3141step1Labels raw3141step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw3142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw3142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3142step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3142step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3142 raw3142Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw3142 raw3142Labels = mixedMoment B raw3142step0 raw3142step0Labels := by
      have hz : ∀ j, raw3142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3142step0 = (fun i j => raw3142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3142step0 raw3142; decide +kernel
      have hl : raw3142step0Labels = raw3142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3142 raw3142Labels permutation346 hz
    mixedMoment B raw3142step0 raw3142step0Labels = mixedMoment B raw3142step1 raw3142step1Labels := by
      have ha : raw3142step1 = (fun i j => raw3142step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3142step1 raw3142step0; decide +kernel
      have hl : raw3142step1Labels = raw3142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3142step0 raw3142step0Labels permutation125 permutation3
    mixedMoment B raw3142step1 raw3142step1Labels = mixedMoment B raw3142step2 raw3142step2Labels := by
      have ha : raw3142step2 = -raw3142step1 := by apply Matrix.ext; change ∀ i j, raw3142step2 i j = -(raw3142step1 i j); unfold raw3142step2 raw3142step1; decide +kernel
      have hl : raw3142step2Labels = raw3142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3142step2 raw3142step2Labels = mixedMoment B raw3142step3 raw3142step3Labels := by
      have ha : raw3142step3 = raw3142step2 := by apply Matrix.ext; unfold raw3142step3 raw3142step2; decide +kernel
      have hl : raw3142step2Labels = labelEmbedding6 ∘ raw3142step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3142step2 raw3142step2Labels raw3142step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw3143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1]]
def raw3143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1]]
def raw3143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3143step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3143 raw3143Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw3143 raw3143Labels = mixedMoment B raw3143step0 raw3143step0Labels := by
      have hz : ∀ j, raw3143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3143step0 = (fun i j => raw3143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3143step0 raw3143; decide +kernel
      have hl : raw3143step0Labels = raw3143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3143 raw3143Labels permutation346 hz
    mixedMoment B raw3143step0 raw3143step0Labels = mixedMoment B raw3143step1 raw3143step1Labels := by
      have ha : raw3143step1 = (fun i j => raw3143step0 (permutation113 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3143step1 raw3143step0; decide +kernel
      have hl : raw3143step1Labels = raw3143step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3143step0 raw3143step0Labels permutation113 permutation5
    mixedMoment B raw3143step1 raw3143step1Labels = mixedMoment B raw3143step2 raw3143step2Labels := by
      have ha : raw3143step2 = raw3143step1 := by apply Matrix.ext; unfold raw3143step2 raw3143step1; decide +kernel
      have hl : raw3143step1Labels = labelEmbedding8 ∘ raw3143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3143step1 raw3143step1Labels raw3143step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw3144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3144step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3144 raw3144Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw3144 raw3144Labels = mixedMoment B raw3144step0 raw3144step0Labels := by
      have hz : ∀ j, raw3144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3144step0 = (fun i j => raw3144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3144step0 raw3144; decide +kernel
      have hl : raw3144step0Labels = raw3144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3144 raw3144Labels permutation346 hz
    mixedMoment B raw3144step0 raw3144step0Labels = mixedMoment B raw3144step1 raw3144step1Labels := by
      have ha : raw3144step1 = (fun i j => raw3144step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3144step1 raw3144step0; decide +kernel
      have hl : raw3144step1Labels = raw3144step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3144step0 raw3144step0Labels permutation38 permutation3
    mixedMoment B raw3144step1 raw3144step1Labels = mixedMoment B raw3144step2 raw3144step2Labels := by
      have ha : raw3144step2 = raw3144step1 := by apply Matrix.ext; unfold raw3144step2 raw3144step1; decide +kernel
      have hl : raw3144step1Labels = labelEmbedding6 ∘ raw3144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3144step1 raw3144step1Labels raw3144step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw3145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3145 raw3145Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw3145 raw3145Labels = mixedMoment B raw3145step0 raw3145step0Labels := by
      have hz : ∀ j, raw3145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3145step0 = (fun i j => raw3145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3145step0 raw3145; decide +kernel
      have hl : raw3145step0Labels = raw3145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3145 raw3145Labels permutation346 hz
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw3146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3146step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3146 raw3146Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw3146 raw3146Labels = mixedMoment B raw3146step0 raw3146step0Labels := by
      have ha : raw3146step0 = (fun i j => raw3146 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3146step0 raw3146; decide +kernel
      have hl : raw3146step0Labels = raw3146Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3146 raw3146Labels permutation182 permutation3
    mixedMoment B raw3146step0 raw3146step0Labels = mixedMoment B raw3146step1 raw3146step1Labels := by
      have ha : raw3146step1 = raw3146step0 := by apply Matrix.ext; unfold raw3146step1 raw3146step0; decide +kernel
      have hl : raw3146step0Labels = labelEmbedding6 ∘ raw3146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3146step0 raw3146step0Labels raw3146step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw3147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3147 raw3147Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw3147 raw3147Labels = mixedMoment B raw3147step0 raw3147step0Labels := by
      have hz : ∀ j, raw3147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3147step0 = (fun i j => raw3147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3147step0 raw3147; decide +kernel
      have hl : raw3147step0Labels = raw3147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3147 raw3147Labels permutation346 hz
    mixedMoment B raw3147step0 raw3147step0Labels = mixedMoment B raw3147step1 raw3147step1Labels := by
      have ha : raw3147step1 = (fun i j => raw3147step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3147step1 raw3147step0; decide +kernel
      have hl : raw3147step1Labels = raw3147step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3147step0 raw3147step0Labels permutation38 permutation3
    mixedMoment B raw3147step1 raw3147step1Labels = mixedMoment B raw3147step2 raw3147step2Labels := by
      have ha : raw3147step2 = raw3147step1 := by apply Matrix.ext; unfold raw3147step2 raw3147step1; decide +kernel
      have hl : raw3147step1Labels = labelEmbedding6 ∘ raw3147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3147step1 raw3147step1Labels raw3147step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw3148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw3148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw3148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3148 raw3148Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw3148 raw3148Labels = mixedMoment B raw3148step0 raw3148step0Labels := by
      have hz : ∀ j, raw3148 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3148step0 = (fun i j => raw3148 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3148step0 raw3148; decide +kernel
      have hl : raw3148step0Labels = raw3148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3148 raw3148Labels permutation520 hz
    mixedMoment B raw3148step0 raw3148step0Labels = mixedMoment B raw3148step1 raw3148step1Labels := by
      have hz : ∀ j, raw3148step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3148step1 = (fun i j => raw3148step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3148step1 raw3148step0; decide +kernel
      have hl : raw3148step1Labels = raw3148step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3148step0 raw3148step0Labels permutation80 hz
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw3149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3149step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3149step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3149 raw3149Labels = mixedMoment B node4054 node4054Labels := by
  calc
    mixedMoment B raw3149 raw3149Labels = mixedMoment B raw3149step0 raw3149step0Labels := by
      have hz : ∀ j, raw3149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3149step0 = (fun i j => raw3149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3149step0 raw3149; decide +kernel
      have hl : raw3149step0Labels = raw3149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3149 raw3149Labels permutation346 hz
    mixedMoment B raw3149step0 raw3149step0Labels = mixedMoment B raw3149step1 raw3149step1Labels := by
      have ha : raw3149step1 = (fun i j => raw3149step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3149step1 raw3149step0; decide +kernel
      have hl : raw3149step1Labels = raw3149step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3149step0 raw3149step0Labels permutation126 permutation3
    mixedMoment B raw3149step1 raw3149step1Labels = mixedMoment B raw3149step2 raw3149step2Labels := by
      have ha : raw3149step2 = -raw3149step1 := by apply Matrix.ext; change ∀ i j, raw3149step2 i j = -(raw3149step1 i j); unfold raw3149step2 raw3149step1; decide +kernel
      have hl : raw3149step2Labels = raw3149step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4054 node4054Labels := by rfl

def raw3150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3150 raw3150Labels = mixedMoment B node4053 node4053Labels := by
  calc
    mixedMoment B raw3150 raw3150Labels = mixedMoment B raw3150step0 raw3150step0Labels := by
      have ha : raw3150step0 = (fun i j => raw3150 (permutation353 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3150step0 raw3150; decide +kernel
      have hl : raw3150step0Labels = raw3150Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3150 raw3150Labels permutation353 permutation3
    _ = mixedMoment B node4053 node4053Labels := by rfl

def raw3151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3151step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3151 raw3151Labels = mixedMoment B node4050 node4050Labels := by
  calc
    mixedMoment B raw3151 raw3151Labels = mixedMoment B raw3151step0 raw3151step0Labels := by
      have hz : ∀ j, raw3151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3151step0 = (fun i j => raw3151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3151step0 raw3151; decide +kernel
      have hl : raw3151step0Labels = raw3151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3151 raw3151Labels permutation346 hz
    mixedMoment B raw3151step0 raw3151step0Labels = mixedMoment B raw3151step1 raw3151step1Labels := by
      have ha : raw3151step1 = (fun i j => raw3151step0 (permutation81 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3151step1 raw3151step0; decide +kernel
      have hl : raw3151step1Labels = raw3151step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3151step0 raw3151step0Labels permutation81 permutation3
    _ = mixedMoment B node4050 node4050Labels := by rfl

def raw3152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3152step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3152step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3152 raw3152Labels = mixedMoment B node4055 node4055Labels := by
  calc
    mixedMoment B raw3152 raw3152Labels = mixedMoment B raw3152step0 raw3152step0Labels := by
      have hz : ∀ j, raw3152 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3152step0 = (fun i j => raw3152 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3152step0 raw3152; decide +kernel
      have hl : raw3152step0Labels = raw3152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3152 raw3152Labels permutation520 hz
    mixedMoment B raw3152step0 raw3152step0Labels = mixedMoment B raw3152step1 raw3152step1Labels := by
      have hz : ∀ j, raw3152step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3152step1 = (fun i j => raw3152step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3152step1 raw3152step0; decide +kernel
      have hl : raw3152step1Labels = raw3152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3152step0 raw3152step0Labels permutation80 hz
    mixedMoment B raw3152step1 raw3152step1Labels = mixedMoment B raw3152step2 raw3152step2Labels := by
      have ha : raw3152step2 = (fun i j => raw3152step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3152step2 raw3152step1; decide +kernel
      have hl : raw3152step2Labels = raw3152step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3152step1 raw3152step1Labels permutation24 permutation6
    _ = mixedMoment B node4055 node4055Labels := by rfl

def raw3153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3153step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3153 raw3153Labels = mixedMoment B node4052 node4052Labels := by
  calc
    mixedMoment B raw3153 raw3153Labels = mixedMoment B raw3153step0 raw3153step0Labels := by
      have hz : ∀ j, raw3153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3153step0 = (fun i j => raw3153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3153step0 raw3153; decide +kernel
      have hl : raw3153step0Labels = raw3153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3153 raw3153Labels permutation346 hz
    mixedMoment B raw3153step0 raw3153step0Labels = mixedMoment B raw3153step1 raw3153step1Labels := by
      have ha : raw3153step1 = (fun i j => raw3153step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3153step1 raw3153step0; decide +kernel
      have hl : raw3153step1Labels = raw3153step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3153step0 raw3153step0Labels permutation102 permutation6
    _ = mixedMoment B node4052 node4052Labels := by rfl

def raw3154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3154step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3154 raw3154Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw3154 raw3154Labels = mixedMoment B raw3154step0 raw3154step0Labels := by
      have hz : ∀ j, raw3154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3154step0 = (fun i j => raw3154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3154step0 raw3154; decide +kernel
      have hl : raw3154step0Labels = raw3154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3154 raw3154Labels permutation346 hz
    mixedMoment B raw3154step0 raw3154step0Labels = mixedMoment B raw3154step1 raw3154step1Labels := by
      have ha : raw3154step1 = (fun i j => raw3154step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3154step1 raw3154step0; decide +kernel
      have hl : raw3154step1Labels = raw3154step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3154step0 raw3154step0Labels permutation43 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw3155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3155 raw3155Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw3155 raw3155Labels = mixedMoment B raw3155step0 raw3155step0Labels := by
      have ha : raw3155step0 = (fun i j => raw3155 (permutation187 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3155step0 raw3155; decide +kernel
      have hl : raw3155step0Labels = raw3155Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3155 raw3155Labels permutation187 permutation3
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw3156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3156 raw3156Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw3156 raw3156Labels = mixedMoment B raw3156step0 raw3156step0Labels := by
      have hz : ∀ j, raw3156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3156step0 = (fun i j => raw3156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3156step0 raw3156; decide +kernel
      have hl : raw3156step0Labels = raw3156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3156 raw3156Labels permutation346 hz
    mixedMoment B raw3156step0 raw3156step0Labels = mixedMoment B raw3156step1 raw3156step1Labels := by
      have ha : raw3156step1 = (fun i j => raw3156step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3156step1 raw3156step0; decide +kernel
      have hl : raw3156step1Labels = raw3156step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3156step0 raw3156step0Labels permutation43 permutation3
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw3157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3157step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3157 raw3157Labels = mixedMoment B node4015 node4015Labels := by
  calc
    mixedMoment B raw3157 raw3157Labels = mixedMoment B raw3157step0 raw3157step0Labels := by
      have hz : ∀ j, raw3157 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3157step0 = (fun i j => raw3157 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3157step0 raw3157; decide +kernel
      have hl : raw3157step0Labels = raw3157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3157 raw3157Labels permutation520 hz
    mixedMoment B raw3157step0 raw3157step0Labels = mixedMoment B raw3157step1 raw3157step1Labels := by
      have hz : ∀ j, raw3157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3157step1 = (fun i j => raw3157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3157step1 raw3157step0; decide +kernel
      have hl : raw3157step1Labels = raw3157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3157step0 raw3157step0Labels permutation80 hz
    mixedMoment B raw3157step1 raw3157step1Labels = mixedMoment B raw3157step2 raw3157step2Labels := by
      have ha : raw3157step2 = (fun i j => raw3157step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3157step2 raw3157step1; decide +kernel
      have hl : raw3157step2Labels = raw3157step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3157step1 raw3157step1Labels permutation11 permutation3
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw3158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3158 raw3158Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw3158 raw3158Labels = mixedMoment B raw3158step0 raw3158step0Labels := by
      have hz : ∀ j, raw3158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3158step0 = (fun i j => raw3158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3158step0 raw3158; decide +kernel
      have hl : raw3158step0Labels = raw3158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3158 raw3158Labels permutation346 hz
    mixedMoment B raw3158step0 raw3158step0Labels = mixedMoment B raw3158step1 raw3158step1Labels := by
      have ha : raw3158step1 = (fun i j => raw3158step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3158step1 raw3158step0; decide +kernel
      have hl : raw3158step1Labels = raw3158step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3158step0 raw3158step0Labels permutation43 permutation3
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw3159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3159 raw3159Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw3159 raw3159Labels = mixedMoment B raw3159step0 raw3159step0Labels := by
      have ha : raw3159step0 = (fun i j => raw3159 (permutation204 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3159step0 raw3159; decide +kernel
      have hl : raw3159step0Labels = raw3159Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3159 raw3159Labels permutation204 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw3160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3160step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3160 raw3160Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw3160 raw3160Labels = mixedMoment B raw3160step0 raw3160step0Labels := by
      have ha : raw3160step0 = (fun i j => raw3160 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3160step0 raw3160; decide +kernel
      have hl : raw3160step0Labels = raw3160Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3160 raw3160Labels permutation162 permutation3
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw3161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3161 raw3161Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw3161 raw3161Labels = mixedMoment B raw3161step0 raw3161step0Labels := by
      have ha : raw3161step0 = (fun i j => raw3161 (permutation204 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3161step0 raw3161; decide +kernel
      have hl : raw3161step0Labels = raw3161Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3161 raw3161Labels permutation204 permutation3
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw3162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw3162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3162 raw3162Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw3162 raw3162Labels = mixedMoment B raw3162step0 raw3162step0Labels := by
      have hz : ∀ j, raw3162 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3162step0 = (fun i j => raw3162 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3162step0 raw3162; decide +kernel
      have hl : raw3162step0Labels = raw3162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3162 raw3162Labels permutation520 hz
    mixedMoment B raw3162step0 raw3162step0Labels = mixedMoment B raw3162step1 raw3162step1Labels := by
      have ha : raw3162step1 = (fun i j => raw3162step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3162step1 raw3162step0; decide +kernel
      have hl : raw3162step1Labels = raw3162step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3162step0 raw3162step0Labels permutation45 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw3163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3163 raw3163Labels = mixedMoment B node4009 node4009Labels := by
  calc
    mixedMoment B raw3163 raw3163Labels = mixedMoment B raw3163step0 raw3163step0Labels := by
      have ha : raw3163step0 = (fun i j => raw3163 (permutation218 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3163step0 raw3163; decide +kernel
      have hl : raw3163step0Labels = raw3163Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3163 raw3163Labels permutation218 permutation3
    _ = mixedMoment B node4009 node4009Labels := by rfl

def raw3164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3164 raw3164Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw3164 raw3164Labels = mixedMoment B raw3164step0 raw3164step0Labels := by
      have hz : ∀ j, raw3164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3164step0 = (fun i j => raw3164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3164step0 raw3164; decide +kernel
      have hl : raw3164step0Labels = raw3164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3164 raw3164Labels permutation346 hz
    mixedMoment B raw3164step0 raw3164step0Labels = mixedMoment B raw3164step1 raw3164step1Labels := by
      have ha : raw3164step1 = (fun i j => raw3164step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3164step1 raw3164step0; decide +kernel
      have hl : raw3164step1Labels = raw3164step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3164step0 raw3164step0Labels permutation33 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw3165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3165 raw3165Labels = mixedMoment B node3999 node3999Labels := by
  calc
    mixedMoment B raw3165 raw3165Labels = mixedMoment B raw3165step0 raw3165step0Labels := by
      have hz : ∀ j, raw3165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3165step0 = (fun i j => raw3165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3165step0 raw3165; decide +kernel
      have hl : raw3165step0Labels = raw3165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3165 raw3165Labels permutation346 hz
    mixedMoment B raw3165step0 raw3165step0Labels = mixedMoment B raw3165step1 raw3165step1Labels := by
      have ha : raw3165step1 = (fun i j => raw3165step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3165step1 raw3165step0; decide +kernel
      have hl : raw3165step1Labels = raw3165step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3165step0 raw3165step0Labels permutation33 permutation3
    _ = mixedMoment B node3999 node3999Labels := by rfl

def raw3166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3166 raw3166Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw3166 raw3166Labels = mixedMoment B raw3166step0 raw3166step0Labels := by
      have ha : raw3166step0 = (fun i j => raw3166 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3166step0 raw3166; decide +kernel
      have hl : raw3166step0Labels = raw3166Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3166 raw3166Labels permutation177 permutation3
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw3167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3167step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3167step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3167 raw3167Labels = mixedMoment B node4018 node4018Labels := by
  calc
    mixedMoment B raw3167 raw3167Labels = mixedMoment B raw3167step0 raw3167step0Labels := by
      have hz : ∀ j, raw3167 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3167step0 = (fun i j => raw3167 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3167step0 raw3167; decide +kernel
      have hl : raw3167step0Labels = raw3167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3167 raw3167Labels permutation520 hz
    mixedMoment B raw3167step0 raw3167step0Labels = mixedMoment B raw3167step1 raw3167step1Labels := by
      have hz : ∀ j, raw3167step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3167step1 = (fun i j => raw3167step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3167step1 raw3167step0; decide +kernel
      have hl : raw3167step1Labels = raw3167step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3167step0 raw3167step0Labels permutation80 hz
    mixedMoment B raw3167step1 raw3167step1Labels = mixedMoment B raw3167step2 raw3167step2Labels := by
      have ha : raw3167step2 = (fun i j => raw3167step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3167step2 raw3167step1; decide +kernel
      have hl : raw3167step2Labels = raw3167step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3167step1 raw3167step1Labels permutation8 permutation3
    _ = mixedMoment B node4018 node4018Labels := by rfl

def raw3168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3168 raw3168Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw3168 raw3168Labels = mixedMoment B raw3168step0 raw3168step0Labels := by
      have hz : ∀ j, raw3168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3168step0 = (fun i j => raw3168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3168step0 raw3168; decide +kernel
      have hl : raw3168step0Labels = raw3168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3168 raw3168Labels permutation346 hz
    mixedMoment B raw3168step0 raw3168step0Labels = mixedMoment B raw3168step1 raw3168step1Labels := by
      have ha : raw3168step1 = (fun i j => raw3168step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3168step1 raw3168step0; decide +kernel
      have hl : raw3168step1Labels = raw3168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3168step0 raw3168step0Labels permutation50 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw3169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3169 raw3169Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw3169 raw3169Labels = mixedMoment B raw3169step0 raw3169step0Labels := by
      have hz : ∀ j, raw3169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3169step0 = (fun i j => raw3169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3169step0 raw3169; decide +kernel
      have hl : raw3169step0Labels = raw3169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3169 raw3169Labels permutation346 hz
    mixedMoment B raw3169step0 raw3169step0Labels = mixedMoment B raw3169step1 raw3169step1Labels := by
      have ha : raw3169step1 = (fun i j => raw3169step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3169step1 raw3169step0; decide +kernel
      have hl : raw3169step1Labels = raw3169step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3169step0 raw3169step0Labels permutation39 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw3170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3170 raw3170Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw3170 raw3170Labels = mixedMoment B raw3170step0 raw3170step0Labels := by
      have hz : ∀ j, raw3170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3170step0 = (fun i j => raw3170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3170step0 raw3170; decide +kernel
      have hl : raw3170step0Labels = raw3170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3170 raw3170Labels permutation346 hz
    mixedMoment B raw3170step0 raw3170step0Labels = mixedMoment B raw3170step1 raw3170step1Labels := by
      have ha : raw3170step1 = (fun i j => raw3170step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3170step1 raw3170step0; decide +kernel
      have hl : raw3170step1Labels = raw3170step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3170step0 raw3170step0Labels permutation127 permutation3
    mixedMoment B raw3170step1 raw3170step1Labels = mixedMoment B raw3170step2 raw3170step2Labels := by
      have ha : raw3170step2 = -raw3170step1 := by apply Matrix.ext; change ∀ i j, raw3170step2 i j = -(raw3170step1 i j); unfold raw3170step2 raw3170step1; decide +kernel
      have hl : raw3170step2Labels = raw3170step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw3171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3171 raw3171Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw3171 raw3171Labels = mixedMoment B raw3171step0 raw3171step0Labels := by
      have ha : raw3171step0 = (fun i j => raw3171 (permutation579 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3171step0 raw3171; decide +kernel
      have hl : raw3171step0Labels = raw3171Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3171 raw3171Labels permutation579 permutation3
    mixedMoment B raw3171step0 raw3171step0Labels = mixedMoment B raw3171step1 raw3171step1Labels := by
      have ha : raw3171step1 = -raw3171step0 := by apply Matrix.ext; change ∀ i j, raw3171step1 i j = -(raw3171step0 i j); unfold raw3171step1 raw3171step0; decide +kernel
      have hl : raw3171step1Labels = raw3171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw3172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw3172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3172 raw3172Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw3172 raw3172Labels = mixedMoment B raw3172step0 raw3172step0Labels := by
      have hz : ∀ j, raw3172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3172step0 = (fun i j => raw3172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3172step0 raw3172; decide +kernel
      have hl : raw3172step0Labels = raw3172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3172 raw3172Labels permutation346 hz
    mixedMoment B raw3172step0 raw3172step0Labels = mixedMoment B raw3172step1 raw3172step1Labels := by
      have ha : raw3172step1 = (fun i j => raw3172step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3172step1 raw3172step0; decide +kernel
      have hl : raw3172step1Labels = raw3172step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3172step0 raw3172step0Labels permutation125 permutation3
    mixedMoment B raw3172step1 raw3172step1Labels = mixedMoment B raw3172step2 raw3172step2Labels := by
      have ha : raw3172step2 = -raw3172step1 := by apply Matrix.ext; change ∀ i j, raw3172step2 i j = -(raw3172step1 i j); unfold raw3172step2 raw3172step1; decide +kernel
      have hl : raw3172step2Labels = raw3172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw3173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1]]
def raw3173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1]]
def raw3173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw3173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw3173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3173 raw3173Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw3173 raw3173Labels = mixedMoment B raw3173step0 raw3173step0Labels := by
      have hz : ∀ j, raw3173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3173step0 = (fun i j => raw3173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3173step0 raw3173; decide +kernel
      have hl : raw3173step0Labels = raw3173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3173 raw3173Labels permutation346 hz
    mixedMoment B raw3173step0 raw3173step0Labels = mixedMoment B raw3173step1 raw3173step1Labels := by
      have ha : raw3173step1 = (fun i j => raw3173step0 (permutation113 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3173step1 raw3173step0; decide +kernel
      have hl : raw3173step1Labels = raw3173step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3173step0 raw3173step0Labels permutation113 permutation3
    mixedMoment B raw3173step1 raw3173step1Labels = mixedMoment B raw3173step2 raw3173step2Labels := by
      have ha : raw3173step2 = -raw3173step1 := by apply Matrix.ext; change ∀ i j, raw3173step2 i j = -(raw3173step1 i j); unfold raw3173step2 raw3173step1; decide +kernel
      have hl : raw3173step2Labels = raw3173step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw3174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3174 raw3174Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw3174 raw3174Labels = mixedMoment B raw3174step0 raw3174step0Labels := by
      have hz : ∀ j, raw3174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3174step0 = (fun i j => raw3174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3174step0 raw3174; decide +kernel
      have hl : raw3174step0Labels = raw3174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3174 raw3174Labels permutation346 hz
    mixedMoment B raw3174step0 raw3174step0Labels = mixedMoment B raw3174step1 raw3174step1Labels := by
      have ha : raw3174step1 = (fun i j => raw3174step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3174step1 raw3174step0; decide +kernel
      have hl : raw3174step1Labels = raw3174step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3174step0 raw3174step0Labels permutation38 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw3175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3175 raw3175Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw3175 raw3175Labels = mixedMoment B raw3175step0 raw3175step0Labels := by
      have hz : ∀ j, raw3175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3175step0 = (fun i j => raw3175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3175step0 raw3175; decide +kernel
      have hl : raw3175step0Labels = raw3175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3175 raw3175Labels permutation346 hz
    mixedMoment B raw3175step0 raw3175step0Labels = mixedMoment B raw3175step1 raw3175step1Labels := by
      have ha : raw3175step1 = (fun i j => raw3175step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3175step1 raw3175step0; decide +kernel
      have hl : raw3175step1Labels = raw3175step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3175step0 raw3175step0Labels permutation151 permutation3
    mixedMoment B raw3175step1 raw3175step1Labels = mixedMoment B raw3175step2 raw3175step2Labels := by
      have ha : raw3175step2 = -raw3175step1 := by apply Matrix.ext; change ∀ i j, raw3175step2 i j = -(raw3175step1 i j); unfold raw3175step2 raw3175step1; decide +kernel
      have hl : raw3175step2Labels = raw3175step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw3176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3176 raw3176Labels = mixedMoment B node3971 node3971Labels := by
  calc
    mixedMoment B raw3176 raw3176Labels = mixedMoment B raw3176step0 raw3176step0Labels := by
      have ha : raw3176step0 = (fun i j => raw3176 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3176step0 raw3176; decide +kernel
      have hl : raw3176step0Labels = raw3176Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3176 raw3176Labels permutation182 permutation3
    _ = mixedMoment B node3971 node3971Labels := by rfl

def raw3177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3177 raw3177Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw3177 raw3177Labels = mixedMoment B raw3177step0 raw3177step0Labels := by
      have hz : ∀ j, raw3177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3177step0 = (fun i j => raw3177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3177step0 raw3177; decide +kernel
      have hl : raw3177step0Labels = raw3177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3177 raw3177Labels permutation346 hz
    mixedMoment B raw3177step0 raw3177step0Labels = mixedMoment B raw3177step1 raw3177step1Labels := by
      have ha : raw3177step1 = (fun i j => raw3177step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3177step1 raw3177step0; decide +kernel
      have hl : raw3177step1Labels = raw3177step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3177step0 raw3177step0Labels permutation38 permutation3
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw3178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw3178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw3178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3178step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3178 raw3178Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw3178 raw3178Labels = mixedMoment B raw3178step0 raw3178step0Labels := by
      have hz : ∀ j, raw3178 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3178step0 = (fun i j => raw3178 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3178step0 raw3178; decide +kernel
      have hl : raw3178step0Labels = raw3178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3178 raw3178Labels permutation520 hz
    mixedMoment B raw3178step0 raw3178step0Labels = mixedMoment B raw3178step1 raw3178step1Labels := by
      have hz : ∀ j, raw3178step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3178step1 = (fun i j => raw3178step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3178step1 raw3178step0; decide +kernel
      have hl : raw3178step1Labels = raw3178step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3178step0 raw3178step0Labels permutation80 hz
    mixedMoment B raw3178step1 raw3178step1Labels = mixedMoment B raw3178step2 raw3178step2Labels := by
      have ha : raw3178step2 = (fun i j => raw3178step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3178step2 raw3178step1; decide +kernel
      have hl : raw3178step2Labels = raw3178step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3178step1 raw3178step1Labels permutation10 permutation3
    _ = mixedMoment B node4014 node4014Labels := by rfl

def raw3179 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw3179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3179step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3179 raw3179Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw3179 raw3179Labels = mixedMoment B raw3179step0 raw3179step0Labels := by
      have hz : ∀ j, raw3179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3179step0 = (fun i j => raw3179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3179step0 raw3179; decide +kernel
      have hl : raw3179step0Labels = raw3179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3179 raw3179Labels permutation346 hz
    mixedMoment B raw3179step0 raw3179step0Labels = mixedMoment B raw3179step1 raw3179step1Labels := by
      have ha : raw3179step1 = (fun i j => raw3179step0 (permutation43 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3179step1 raw3179step0; decide +kernel
      have hl : raw3179step1Labels = raw3179step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3179step0 raw3179step0Labels permutation43 permutation2
    mixedMoment B raw3179step1 raw3179step1Labels = mixedMoment B raw3179step2 raw3179step2Labels := by
      have ha : raw3179step2 = -raw3179step1 := by apply Matrix.ext; change ∀ i j, raw3179step2 i j = -(raw3179step1 i j); unfold raw3179step2 raw3179step1; decide +kernel
      have hl : raw3179step2Labels = raw3179step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw3180 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3180 raw3180Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3180 raw3180Labels = mixedMoment B raw3180step0 raw3180step0Labels := by
      have ha : raw3180step0 = (fun i j => raw3180 (permutation218 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3180step0 raw3180; decide +kernel
      have hl : raw3180step0Labels = raw3180Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3180 raw3180Labels permutation218 permutation2
    mixedMoment B raw3180step0 raw3180step0Labels = mixedMoment B raw3180step1 raw3180step1Labels := by
      have ha : raw3180step1 = -raw3180step0 := by apply Matrix.ext; change ∀ i j, raw3180step1 i j = -(raw3180step0 i j); unfold raw3180step1 raw3180step0; decide +kernel
      have hl : raw3180step1Labels = raw3180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3181 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3181step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3181step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3181 raw3181Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw3181 raw3181Labels = mixedMoment B raw3181step0 raw3181step0Labels := by
      have hz : ∀ j, raw3181 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3181step0 = (fun i j => raw3181 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3181step0 raw3181; decide +kernel
      have hl : raw3181step0Labels = raw3181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3181 raw3181Labels permutation434 hz
    mixedMoment B raw3181step0 raw3181step0Labels = mixedMoment B raw3181step1 raw3181step1Labels := by
      have hz : ∀ j, raw3181step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3181step1 = (fun i j => raw3181step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3181step1 raw3181step0; decide +kernel
      have hl : raw3181step1Labels = raw3181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3181step0 raw3181step0Labels permutation80 hz
    mixedMoment B raw3181step1 raw3181step1Labels = mixedMoment B raw3181step2 raw3181step2Labels := by
      have ha : raw3181step2 = (fun i j => raw3181step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3181step2 raw3181step1; decide +kernel
      have hl : raw3181step2Labels = raw3181step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3181step1 raw3181step1Labels permutation12 permutation2
    mixedMoment B raw3181step2 raw3181step2Labels = mixedMoment B raw3181step3 raw3181step3Labels := by
      have ha : raw3181step3 = -raw3181step2 := by apply Matrix.ext; change ∀ i j, raw3181step3 i j = -(raw3181step2 i j); unfold raw3181step3 raw3181step2; decide +kernel
      have hl : raw3181step3Labels = raw3181step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw3182 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3182step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3182 raw3182Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3182 raw3182Labels = mixedMoment B raw3182step0 raw3182step0Labels := by
      have hz : ∀ j, raw3182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3182step0 = (fun i j => raw3182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3182step0 raw3182; decide +kernel
      have hl : raw3182step0Labels = raw3182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3182 raw3182Labels permutation346 hz
    mixedMoment B raw3182step0 raw3182step0Labels = mixedMoment B raw3182step1 raw3182step1Labels := by
      have ha : raw3182step1 = (fun i j => raw3182step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3182step1 raw3182step0; decide +kernel
      have hl : raw3182step1Labels = raw3182step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3182step0 raw3182step0Labels permutation42 permutation2
    mixedMoment B raw3182step1 raw3182step1Labels = mixedMoment B raw3182step2 raw3182step2Labels := by
      have ha : raw3182step2 = -raw3182step1 := by apply Matrix.ext; change ∀ i j, raw3182step2 i j = -(raw3182step1 i j); unfold raw3182step2 raw3182step1; decide +kernel
      have hl : raw3182step2Labels = raw3182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3183 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3183step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3183 raw3183Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw3183 raw3183Labels = mixedMoment B raw3183step0 raw3183step0Labels := by
      have hz : ∀ j, raw3183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3183step0 = (fun i j => raw3183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3183step0 raw3183; decide +kernel
      have hl : raw3183step0Labels = raw3183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3183 raw3183Labels permutation346 hz
    mixedMoment B raw3183step0 raw3183step0Labels = mixedMoment B raw3183step1 raw3183step1Labels := by
      have ha : raw3183step1 = (fun i j => raw3183step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3183step1 raw3183step0; decide +kernel
      have hl : raw3183step1Labels = raw3183step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3183step0 raw3183step0Labels permutation38 permutation2
    mixedMoment B raw3183step1 raw3183step1Labels = mixedMoment B raw3183step2 raw3183step2Labels := by
      have ha : raw3183step2 = -raw3183step1 := by apply Matrix.ext; change ∀ i j, raw3183step2 i j = -(raw3183step1 i j); unfold raw3183step2 raw3183step1; decide +kernel
      have hl : raw3183step2Labels = raw3183step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw3184 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3184step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3184step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3184step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3184step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3184 raw3184Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw3184 raw3184Labels = mixedMoment B raw3184step0 raw3184step0Labels := by
      have hz : ∀ j, raw3184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3184step0 = (fun i j => raw3184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3184step0 raw3184; decide +kernel
      have hl : raw3184step0Labels = raw3184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3184 raw3184Labels permutation346 hz
    mixedMoment B raw3184step0 raw3184step0Labels = mixedMoment B raw3184step1 raw3184step1Labels := by
      have hz : ∀ j, raw3184step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3184step1 = (fun i j => raw3184step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3184step1 raw3184step0; decide +kernel
      have hl : raw3184step1Labels = raw3184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3184step0 raw3184step0Labels permutation56 hz
    mixedMoment B raw3184step1 raw3184step1Labels = mixedMoment B raw3184step2 raw3184step2Labels := by
      have ha : raw3184step2 = (fun i j => raw3184step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3184step2 raw3184step1; decide +kernel
      have hl : raw3184step2Labels = raw3184step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3184step1 raw3184step1Labels permutation10 permutation4
    mixedMoment B raw3184step2 raw3184step2Labels = mixedMoment B raw3184step3 raw3184step3Labels := by
      have ha : raw3184step3 = -raw3184step2 := by apply Matrix.ext; change ∀ i j, raw3184step3 i j = -(raw3184step2 i j); unfold raw3184step3 raw3184step2; decide +kernel
      have hl : raw3184step3Labels = raw3184step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3184step3 raw3184step3Labels = mixedMoment B raw3184step4 raw3184step4Labels := by
      have ha : raw3184step4 = raw3184step3 := by apply Matrix.ext; unfold raw3184step4 raw3184step3; decide +kernel
      have hl : raw3184step3Labels = labelEmbedding7 ∘ raw3184step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3184step3 raw3184step3Labels raw3184step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw3185 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3185step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3185step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3185 raw3185Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3185 raw3185Labels = mixedMoment B raw3185step0 raw3185step0Labels := by
      have hz : ∀ j, raw3185 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3185step0 = (fun i j => raw3185 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3185step0 raw3185; decide +kernel
      have hl : raw3185step0Labels = raw3185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3185 raw3185Labels permutation265 hz
    mixedMoment B raw3185step0 raw3185step0Labels = mixedMoment B raw3185step1 raw3185step1Labels := by
      have ha : raw3185step1 = (fun i j => raw3185step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3185step1 raw3185step0; decide +kernel
      have hl : raw3185step1Labels = raw3185step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3185step0 raw3185step0Labels permutation32 permutation6
    mixedMoment B raw3185step1 raw3185step1Labels = mixedMoment B raw3185step2 raw3185step2Labels := by
      have ha : raw3185step2 = raw3185step1 := by apply Matrix.ext; unfold raw3185step2 raw3185step1; decide +kernel
      have hl : raw3185step1Labels = labelEmbedding9 ∘ raw3185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3185step1 raw3185step1Labels raw3185step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3186 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3186step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 0, 1], ![0, -1, 1]]
def raw3186step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3186step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3186step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3186step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3186step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3186 raw3186Labels = mixedMoment B node5495 node5495Labels := by
  calc
    mixedMoment B raw3186 raw3186Labels = mixedMoment B raw3186step0 raw3186step0Labels := by
      have hz : ∀ j, raw3186 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3186step0 = (fun i j => raw3186 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3186step0 raw3186; decide +kernel
      have hl : raw3186step0Labels = raw3186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3186 raw3186Labels permutation434 hz
    mixedMoment B raw3186step0 raw3186step0Labels = mixedMoment B raw3186step1 raw3186step1Labels := by
      have hz : ∀ j, raw3186step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3186step1 = (fun i j => raw3186step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3186step1 raw3186step0; decide +kernel
      have hl : raw3186step1Labels = raw3186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3186step0 raw3186step0Labels permutation80 hz
    mixedMoment B raw3186step1 raw3186step1Labels = mixedMoment B raw3186step2 raw3186step2Labels := by
      have hz : ∀ j, raw3186step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3186step2 = (fun i j => raw3186step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3186step2 raw3186step1; decide +kernel
      have hl : raw3186step2Labels = raw3186step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3186step1 raw3186step1Labels permutation14 hz
    mixedMoment B raw3186step2 raw3186step2Labels = mixedMoment B raw3186step3 raw3186step3Labels := by
      have ha : raw3186step3 = (fun i j => raw3186step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3186step3 raw3186step2; decide +kernel
      have hl : raw3186step3Labels = raw3186step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3186step2 raw3186step2Labels permutation2 permutation6
    mixedMoment B raw3186step3 raw3186step3Labels = mixedMoment B raw3186step4 raw3186step4Labels := by
      have ha : raw3186step4 = raw3186step3 := by apply Matrix.ext; unfold raw3186step4 raw3186step3; decide +kernel
      have hl : raw3186step3Labels = labelEmbedding9 ∘ raw3186step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3186step3 raw3186step3Labels raw3186step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5495 node5495Labels := by rfl

def raw3187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3187step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3187 raw3187Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3187 raw3187Labels = mixedMoment B raw3187step0 raw3187step0Labels := by
      have hz : ∀ j, raw3187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3187step0 = (fun i j => raw3187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3187step0 raw3187; decide +kernel
      have hl : raw3187step0Labels = raw3187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3187 raw3187Labels permutation346 hz
    mixedMoment B raw3187step0 raw3187step0Labels = mixedMoment B raw3187step1 raw3187step1Labels := by
      have hz : ∀ j, raw3187step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3187step1 = (fun i j => raw3187step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3187step1 raw3187step0; decide +kernel
      have hl : raw3187step1Labels = raw3187step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3187step0 raw3187step0Labels permutation56 hz
    mixedMoment B raw3187step1 raw3187step1Labels = mixedMoment B raw3187step2 raw3187step2Labels := by
      have ha : raw3187step2 = (fun i j => raw3187step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3187step2 raw3187step1; decide +kernel
      have hl : raw3187step2Labels = raw3187step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3187step1 raw3187step1Labels permutation25 permutation2
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3188step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3188step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3188step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3188step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3188 raw3188Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw3188 raw3188Labels = mixedMoment B raw3188step0 raw3188step0Labels := by
      have hz : ∀ j, raw3188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3188step0 = (fun i j => raw3188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3188step0 raw3188; decide +kernel
      have hl : raw3188step0Labels = raw3188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3188 raw3188Labels permutation346 hz
    mixedMoment B raw3188step0 raw3188step0Labels = mixedMoment B raw3188step1 raw3188step1Labels := by
      have hz : ∀ j, raw3188step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3188step1 = (fun i j => raw3188step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3188step1 raw3188step0; decide +kernel
      have hl : raw3188step1Labels = raw3188step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3188step0 raw3188step0Labels permutation56 hz
    mixedMoment B raw3188step1 raw3188step1Labels = mixedMoment B raw3188step2 raw3188step2Labels := by
      have ha : raw3188step2 = (fun i j => raw3188step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3188step2 raw3188step1; decide +kernel
      have hl : raw3188step2Labels = raw3188step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3188step1 raw3188step1Labels permutation8 permutation7
    mixedMoment B raw3188step2 raw3188step2Labels = mixedMoment B raw3188step3 raw3188step3Labels := by
      have ha : raw3188step3 = raw3188step2 := by apply Matrix.ext; unfold raw3188step3 raw3188step2; decide +kernel
      have hl : raw3188step2Labels = labelEmbedding10 ∘ raw3188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3188step2 raw3188step2Labels raw3188step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw3189 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3189step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3189step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3189step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3189 raw3189Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3189 raw3189Labels = mixedMoment B raw3189step0 raw3189step0Labels := by
      have ha : raw3189step0 = (fun i j => raw3189 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3189step0 raw3189; decide +kernel
      have hl : raw3189step0Labels = raw3189Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3189 raw3189Labels permutation164 permutation4
    mixedMoment B raw3189step0 raw3189step0Labels = mixedMoment B raw3189step1 raw3189step1Labels := by
      have ha : raw3189step1 = -raw3189step0 := by apply Matrix.ext; change ∀ i j, raw3189step1 i j = -(raw3189step0 i j); unfold raw3189step1 raw3189step0; decide +kernel
      have hl : raw3189step1Labels = raw3189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3189step1 raw3189step1Labels = mixedMoment B raw3189step2 raw3189step2Labels := by
      have ha : raw3189step2 = raw3189step1 := by apply Matrix.ext; unfold raw3189step2 raw3189step1; decide +kernel
      have hl : raw3189step1Labels = labelEmbedding7 ∘ raw3189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3189step1 raw3189step1Labels raw3189step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3190step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3190 raw3190Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw3190 raw3190Labels = mixedMoment B raw3190step0 raw3190step0Labels := by
      have ha : raw3190step0 = (fun i j => raw3190 (permutation329 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3190step0 raw3190; decide +kernel
      have hl : raw3190step0Labels = raw3190Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3190 raw3190Labels permutation329 permutation3
    mixedMoment B raw3190step0 raw3190step0Labels = mixedMoment B raw3190step1 raw3190step1Labels := by
      have ha : raw3190step1 = raw3190step0 := by apply Matrix.ext; unfold raw3190step1 raw3190step0; decide +kernel
      have hl : raw3190step0Labels = labelEmbedding6 ∘ raw3190step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3190step0 raw3190step0Labels raw3190step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw3191 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3191step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3191 raw3191Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3191 raw3191Labels = mixedMoment B raw3191step0 raw3191step0Labels := by
      have hz : ∀ j, raw3191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3191step0 = (fun i j => raw3191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3191step0 raw3191; decide +kernel
      have hl : raw3191step0Labels = raw3191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3191 raw3191Labels permutation434 hz
    mixedMoment B raw3191step0 raw3191step0Labels = mixedMoment B raw3191step1 raw3191step1Labels := by
      have ha : raw3191step1 = (fun i j => raw3191step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3191step1 raw3191step0; decide +kernel
      have hl : raw3191step1Labels = raw3191step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3191step0 raw3191step0Labels permutation32 permutation6
    mixedMoment B raw3191step1 raw3191step1Labels = mixedMoment B raw3191step2 raw3191step2Labels := by
      have ha : raw3191step2 = raw3191step1 := by apply Matrix.ext; unfold raw3191step2 raw3191step1; decide +kernel
      have hl : raw3191step1Labels = labelEmbedding9 ∘ raw3191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3191step1 raw3191step1Labels raw3191step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3192 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3192step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3192 raw3192Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw3192 raw3192Labels = mixedMoment B raw3192step0 raw3192step0Labels := by
      have ha : raw3192step0 = (fun i j => raw3192 (permutation538 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3192step0 raw3192; decide +kernel
      have hl : raw3192step0Labels = raw3192Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3192 raw3192Labels permutation538 permutation3
    mixedMoment B raw3192step0 raw3192step0Labels = mixedMoment B raw3192step1 raw3192step1Labels := by
      have ha : raw3192step1 = raw3192step0 := by apply Matrix.ext; unfold raw3192step1 raw3192step0; decide +kernel
      have hl : raw3192step0Labels = labelEmbedding6 ∘ raw3192step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3192step0 raw3192step0Labels raw3192step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw3193 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3193step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3193 raw3193Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3193 raw3193Labels = mixedMoment B raw3193step0 raw3193step0Labels := by
      have ha : raw3193step0 = (fun i j => raw3193 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3193step0 raw3193; decide +kernel
      have hl : raw3193step0Labels = raw3193Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3193 raw3193Labels permutation182 permutation7
    mixedMoment B raw3193step0 raw3193step0Labels = mixedMoment B raw3193step1 raw3193step1Labels := by
      have ha : raw3193step1 = raw3193step0 := by apply Matrix.ext; unfold raw3193step1 raw3193step0; decide +kernel
      have hl : raw3193step0Labels = labelEmbedding10 ∘ raw3193step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3193step0 raw3193step0Labels raw3193step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw3194 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw3194step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3194step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3194step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3194step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3194 raw3194Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw3194 raw3194Labels = mixedMoment B raw3194step0 raw3194step0Labels := by
      have hz : ∀ j, raw3194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3194step0 = (fun i j => raw3194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3194step0 raw3194; decide +kernel
      have hl : raw3194step0Labels = raw3194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3194 raw3194Labels permutation346 hz
    mixedMoment B raw3194step0 raw3194step0Labels = mixedMoment B raw3194step1 raw3194step1Labels := by
      have ha : raw3194step1 = (fun i j => raw3194step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3194step1 raw3194step0; decide +kernel
      have hl : raw3194step1Labels = raw3194step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3194step0 raw3194step0Labels permutation35 permutation4
    mixedMoment B raw3194step1 raw3194step1Labels = mixedMoment B raw3194step2 raw3194step2Labels := by
      have ha : raw3194step2 = -raw3194step1 := by apply Matrix.ext; change ∀ i j, raw3194step2 i j = -(raw3194step1 i j); unfold raw3194step2 raw3194step1; decide +kernel
      have hl : raw3194step2Labels = raw3194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3194step2 raw3194step2Labels = mixedMoment B raw3194step3 raw3194step3Labels := by
      have ha : raw3194step3 = raw3194step2 := by apply Matrix.ext; unfold raw3194step3 raw3194step2; decide +kernel
      have hl : raw3194step2Labels = labelEmbedding7 ∘ raw3194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3194step2 raw3194step2Labels raw3194step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw3195 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw3195step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw3195step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3195 raw3195Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw3195 raw3195Labels = mixedMoment B raw3195step0 raw3195step0Labels := by
      have hz : ∀ j, raw3195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3195step0 = (fun i j => raw3195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3195step0 raw3195; decide +kernel
      have hl : raw3195step0Labels = raw3195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3195 raw3195Labels permutation346 hz
    mixedMoment B raw3195step0 raw3195step0Labels = mixedMoment B raw3195step1 raw3195step1Labels := by
      have ha : raw3195step1 = (fun i j => raw3195step0 (permutation72 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3195step1 raw3195step0; decide +kernel
      have hl : raw3195step1Labels = raw3195step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3195step0 raw3195step0Labels permutation72 permutation3
    mixedMoment B raw3195step1 raw3195step1Labels = mixedMoment B raw3195step2 raw3195step2Labels := by
      have ha : raw3195step2 = raw3195step1 := by apply Matrix.ext; unfold raw3195step2 raw3195step1; decide +kernel
      have hl : raw3195step1Labels = labelEmbedding6 ∘ raw3195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3195step1 raw3195step1Labels raw3195step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw3196 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3196step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3196 raw3196Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw3196 raw3196Labels = mixedMoment B raw3196step0 raw3196step0Labels := by
      have ha : raw3196step0 = (fun i j => raw3196 (permutation514 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3196step0 raw3196; decide +kernel
      have hl : raw3196step0Labels = raw3196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3196 raw3196Labels permutation514 permutation5
    mixedMoment B raw3196step0 raw3196step0Labels = mixedMoment B raw3196step1 raw3196step1Labels := by
      have ha : raw3196step1 = raw3196step0 := by apply Matrix.ext; unfold raw3196step1 raw3196step0; decide +kernel
      have hl : raw3196step0Labels = labelEmbedding8 ∘ raw3196step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3196step0 raw3196step0Labels raw3196step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw3197 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1]]
def raw3197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3197step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3197 raw3197Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw3197 raw3197Labels = mixedMoment B raw3197step0 raw3197step0Labels := by
      have hz : ∀ j, raw3197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3197step0 = (fun i j => raw3197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3197step0 raw3197; decide +kernel
      have hl : raw3197step0Labels = raw3197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3197 raw3197Labels permutation346 hz
    mixedMoment B raw3197step0 raw3197step0Labels = mixedMoment B raw3197step1 raw3197step1Labels := by
      have ha : raw3197step1 = (fun i j => raw3197step0 (permutation98 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3197step1 raw3197step0; decide +kernel
      have hl : raw3197step1Labels = raw3197step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3197step0 raw3197step0Labels permutation98 permutation5
    mixedMoment B raw3197step1 raw3197step1Labels = mixedMoment B raw3197step2 raw3197step2Labels := by
      have ha : raw3197step2 = raw3197step1 := by apply Matrix.ext; unfold raw3197step2 raw3197step1; decide +kernel
      have hl : raw3197step1Labels = labelEmbedding8 ∘ raw3197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3197step1 raw3197step1Labels raw3197step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw3198 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3198step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3198step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3198step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3198 raw3198Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw3198 raw3198Labels = mixedMoment B raw3198step0 raw3198step0Labels := by
      have hz : ∀ j, raw3198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3198step0 = (fun i j => raw3198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3198step0 raw3198; decide +kernel
      have hl : raw3198step0Labels = raw3198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3198 raw3198Labels permutation346 hz
    mixedMoment B raw3198step0 raw3198step0Labels = mixedMoment B raw3198step1 raw3198step1Labels := by
      have ha : raw3198step1 = (fun i j => raw3198step0 (permutation83 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3198step1 raw3198step0; decide +kernel
      have hl : raw3198step1Labels = raw3198step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3198step0 raw3198step0Labels permutation83 permutation3
    mixedMoment B raw3198step1 raw3198step1Labels = mixedMoment B raw3198step2 raw3198step2Labels := by
      have ha : raw3198step2 = -raw3198step1 := by apply Matrix.ext; change ∀ i j, raw3198step2 i j = -(raw3198step1 i j); unfold raw3198step2 raw3198step1; decide +kernel
      have hl : raw3198step2Labels = raw3198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3198step2 raw3198step2Labels = mixedMoment B raw3198step3 raw3198step3Labels := by
      have ha : raw3198step3 = raw3198step2 := by apply Matrix.ext; unfold raw3198step3 raw3198step2; decide +kernel
      have hl : raw3198step2Labels = labelEmbedding6 ∘ raw3198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3198step2 raw3198step2Labels raw3198step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw3199 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3199step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3199step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3199step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3199step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3199 raw3199Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw3199 raw3199Labels = mixedMoment B raw3199step0 raw3199step0Labels := by
      have hz : ∀ j, raw3199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3199step0 = (fun i j => raw3199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3199step0 raw3199; decide +kernel
      have hl : raw3199step0Labels = raw3199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3199 raw3199Labels permutation346 hz
    mixedMoment B raw3199step0 raw3199step0Labels = mixedMoment B raw3199step1 raw3199step1Labels := by
      have ha : raw3199step1 = (fun i j => raw3199step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3199step1 raw3199step0; decide +kernel
      have hl : raw3199step1Labels = raw3199step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3199step0 raw3199step0Labels permutation32 permutation4
    mixedMoment B raw3199step1 raw3199step1Labels = mixedMoment B raw3199step2 raw3199step2Labels := by
      have ha : raw3199step2 = -raw3199step1 := by apply Matrix.ext; change ∀ i j, raw3199step2 i j = -(raw3199step1 i j); unfold raw3199step2 raw3199step1; decide +kernel
      have hl : raw3199step2Labels = raw3199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3199step2 raw3199step2Labels = mixedMoment B raw3199step3 raw3199step3Labels := by
      have ha : raw3199step3 = raw3199step2 := by apply Matrix.ext; unfold raw3199step3 raw3199step2; decide +kernel
      have hl : raw3199step2Labels = labelEmbedding7 ∘ raw3199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3199step2 raw3199step2Labels raw3199step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
