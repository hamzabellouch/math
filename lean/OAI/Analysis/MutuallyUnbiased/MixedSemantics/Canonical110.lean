import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14080 raw14080Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw14080 raw14080Labels = mixedMoment B raw14080step0 raw14080step0Labels := by
      have ha : raw14080step0 = (fun i j => raw14080 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14080step0 raw14080; decide +kernel
      have hl : raw14080step0Labels = raw14080Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14080 raw14080Labels permutation183 permutation2
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw14081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14081 raw14081Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw14081 raw14081Labels = mixedMoment B raw14081step0 raw14081step0Labels := by
      have ha : raw14081step0 = (fun i j => raw14081 (permutation189 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14081step0 raw14081; decide +kernel
      have hl : raw14081step0Labels = raw14081Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14081 raw14081Labels permutation189 permutation2
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw14082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14082 raw14082Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw14082 raw14082Labels = mixedMoment B raw14082step0 raw14082step0Labels := by
      have hz : ∀ j, raw14082 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14082step0 = (fun i j => raw14082 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14082step0 raw14082; decide +kernel
      have hl : raw14082step0Labels = raw14082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14082 raw14082Labels permutation590 hz
    mixedMoment B raw14082step0 raw14082step0Labels = mixedMoment B raw14082step1 raw14082step1Labels := by
      have ha : raw14082step1 = (fun i j => raw14082step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14082step1 raw14082step0; decide +kernel
      have hl : raw14082step1Labels = raw14082step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14082step0 raw14082step0Labels permutation39 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw14083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14083 raw14083Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw14083 raw14083Labels = mixedMoment B raw14083step0 raw14083step0Labels := by
      have hz : ∀ j, raw14083 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14083step0 = (fun i j => raw14083 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14083step0 raw14083; decide +kernel
      have hl : raw14083step0Labels = raw14083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14083 raw14083Labels permutation265 hz
    mixedMoment B raw14083step0 raw14083step0Labels = mixedMoment B raw14083step1 raw14083step1Labels := by
      have ha : raw14083step1 = (fun i j => raw14083step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14083step1 raw14083step0; decide +kernel
      have hl : raw14083step1Labels = raw14083step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14083step0 raw14083step0Labels permutation37 permutation2
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw14084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14084 raw14084Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw14084 raw14084Labels = mixedMoment B raw14084step0 raw14084step0Labels := by
      have ha : raw14084step0 = (fun i j => raw14084 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14084step0 raw14084; decide +kernel
      have hl : raw14084step0Labels = raw14084Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14084 raw14084Labels permutation157 permutation2
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw14085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14085 raw14085Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw14085 raw14085Labels = mixedMoment B raw14085step0 raw14085step0Labels := by
      have hz : ∀ j, raw14085 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14085step0 = (fun i j => raw14085 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14085step0 raw14085; decide +kernel
      have hl : raw14085step0Labels = raw14085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14085 raw14085Labels permutation265 hz
    mixedMoment B raw14085step0 raw14085step0Labels = mixedMoment B raw14085step1 raw14085step1Labels := by
      have ha : raw14085step1 = (fun i j => raw14085step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14085step1 raw14085step0; decide +kernel
      have hl : raw14085step1Labels = raw14085step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14085step0 raw14085step0Labels permutation39 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw14086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14086 raw14086Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw14086 raw14086Labels = mixedMoment B raw14086step0 raw14086step0Labels := by
      have hz : ∀ j, raw14086 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14086step0 = (fun i j => raw14086 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14086step0 raw14086; decide +kernel
      have hl : raw14086step0Labels = raw14086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14086 raw14086Labels permutation265 hz
    mixedMoment B raw14086step0 raw14086step0Labels = mixedMoment B raw14086step1 raw14086step1Labels := by
      have ha : raw14086step1 = (fun i j => raw14086step0 (permutation45 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14086step1 raw14086step0; decide +kernel
      have hl : raw14086step1Labels = raw14086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14086step0 raw14086step0Labels permutation45 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw14087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14087step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14087step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14087 raw14087Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw14087 raw14087Labels = mixedMoment B raw14087step0 raw14087step0Labels := by
      have hz : ∀ j, raw14087 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14087step0 = (fun i j => raw14087 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14087step0 raw14087; decide +kernel
      have hl : raw14087step0Labels = raw14087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14087 raw14087Labels permutation590 hz
    mixedMoment B raw14087step0 raw14087step0Labels = mixedMoment B raw14087step1 raw14087step1Labels := by
      have hz : ∀ j, raw14087step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14087step1 = (fun i j => raw14087step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14087step1 raw14087step0; decide +kernel
      have hl : raw14087step1Labels = raw14087step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14087step0 raw14087step0Labels permutation56 hz
    mixedMoment B raw14087step1 raw14087step1Labels = mixedMoment B raw14087step2 raw14087step2Labels := by
      have ha : raw14087step2 = (fun i j => raw14087step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14087step2 raw14087step1; decide +kernel
      have hl : raw14087step2Labels = raw14087step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14087step1 raw14087step1Labels permutation9 permutation2
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw14088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14088 raw14088Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw14088 raw14088Labels = mixedMoment B raw14088step0 raw14088step0Labels := by
      have hz : ∀ j, raw14088 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14088step0 = (fun i j => raw14088 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14088step0 raw14088; decide +kernel
      have hl : raw14088step0Labels = raw14088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14088 raw14088Labels permutation265 hz
    mixedMoment B raw14088step0 raw14088step0Labels = mixedMoment B raw14088step1 raw14088step1Labels := by
      have ha : raw14088step1 = (fun i j => raw14088step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14088step1 raw14088step0; decide +kernel
      have hl : raw14088step1Labels = raw14088step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14088step0 raw14088step0Labels permutation37 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw14089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14089 raw14089Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw14089 raw14089Labels = mixedMoment B raw14089step0 raw14089step0Labels := by
      have ha : raw14089step0 = (fun i j => raw14089 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14089step0 raw14089; decide +kernel
      have hl : raw14089step0Labels = raw14089Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14089 raw14089Labels permutation157 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw14090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14090 raw14090Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw14090 raw14090Labels = mixedMoment B raw14090step0 raw14090step0Labels := by
      have hz : ∀ j, raw14090 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14090step0 = (fun i j => raw14090 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14090step0 raw14090; decide +kernel
      have hl : raw14090step0Labels = raw14090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14090 raw14090Labels permutation265 hz
    mixedMoment B raw14090step0 raw14090step0Labels = mixedMoment B raw14090step1 raw14090step1Labels := by
      have ha : raw14090step1 = (fun i j => raw14090step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14090step1 raw14090step0; decide +kernel
      have hl : raw14090step1Labels = raw14090step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14090step0 raw14090step0Labels permutation37 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw14091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14091 raw14091Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw14091 raw14091Labels = mixedMoment B raw14091step0 raw14091step0Labels := by
      have hz : ∀ j, raw14091 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14091step0 = (fun i j => raw14091 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14091step0 raw14091; decide +kernel
      have hl : raw14091step0Labels = raw14091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14091 raw14091Labels permutation265 hz
    mixedMoment B raw14091step0 raw14091step0Labels = mixedMoment B raw14091step1 raw14091step1Labels := by
      have ha : raw14091step1 = (fun i j => raw14091step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14091step1 raw14091step0; decide +kernel
      have hl : raw14091step1Labels = raw14091step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14091step0 raw14091step0Labels permutation35 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw14092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw14092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw14092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14092 raw14092Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw14092 raw14092Labels = mixedMoment B raw14092step0 raw14092step0Labels := by
      have hz : ∀ j, raw14092 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14092step0 = (fun i j => raw14092 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14092step0 raw14092; decide +kernel
      have hl : raw14092step0Labels = raw14092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14092 raw14092Labels permutation590 hz
    mixedMoment B raw14092step0 raw14092step0Labels = mixedMoment B raw14092step1 raw14092step1Labels := by
      have hz : ∀ j, raw14092step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14092step1 = (fun i j => raw14092step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14092step1 raw14092step0; decide +kernel
      have hl : raw14092step1Labels = raw14092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14092step0 raw14092step0Labels permutation56 hz
    mixedMoment B raw14092step1 raw14092step1Labels = mixedMoment B raw14092step2 raw14092step2Labels := by
      have ha : raw14092step2 = (fun i j => raw14092step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14092step2 raw14092step1; decide +kernel
      have hl : raw14092step2Labels = raw14092step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14092step1 raw14092step1Labels permutation9 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw14093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14093 raw14093Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw14093 raw14093Labels = mixedMoment B raw14093step0 raw14093step0Labels := by
      have hz : ∀ j, raw14093 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14093step0 = (fun i j => raw14093 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14093step0 raw14093; decide +kernel
      have hl : raw14093step0Labels = raw14093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14093 raw14093Labels permutation265 hz
    mixedMoment B raw14093step0 raw14093step0Labels = mixedMoment B raw14093step1 raw14093step1Labels := by
      have ha : raw14093step1 = (fun i j => raw14093step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14093step1 raw14093step0; decide +kernel
      have hl : raw14093step1Labels = raw14093step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14093step0 raw14093step0Labels permutation36 permutation2
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw14094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14094 raw14094Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw14094 raw14094Labels = mixedMoment B raw14094step0 raw14094step0Labels := by
      have ha : raw14094step0 = (fun i j => raw14094 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14094step0 raw14094; decide +kernel
      have hl : raw14094step0Labels = raw14094Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14094 raw14094Labels permutation156 permutation2
    _ = mixedMoment B node5135 node5135Labels := by rfl

def raw14095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14095 raw14095Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw14095 raw14095Labels = mixedMoment B raw14095step0 raw14095step0Labels := by
      have hz : ∀ j, raw14095 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14095step0 = (fun i j => raw14095 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14095step0 raw14095; decide +kernel
      have hl : raw14095step0Labels = raw14095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14095 raw14095Labels permutation265 hz
    mixedMoment B raw14095step0 raw14095step0Labels = mixedMoment B raw14095step1 raw14095step1Labels := by
      have ha : raw14095step1 = (fun i j => raw14095step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14095step1 raw14095step0; decide +kernel
      have hl : raw14095step1Labels = raw14095step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14095step0 raw14095step0Labels permutation36 permutation2
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw14096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14096 raw14096Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw14096 raw14096Labels = mixedMoment B raw14096step0 raw14096step0Labels := by
      have hz : ∀ j, raw14096 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14096step0 = (fun i j => raw14096 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14096step0 raw14096; decide +kernel
      have hl : raw14096step0Labels = raw14096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14096 raw14096Labels permutation265 hz
    mixedMoment B raw14096step0 raw14096step0Labels = mixedMoment B raw14096step1 raw14096step1Labels := by
      have ha : raw14096step1 = (fun i j => raw14096step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14096step1 raw14096step0; decide +kernel
      have hl : raw14096step1Labels = raw14096step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14096step0 raw14096step0Labels permutation33 permutation2
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw14097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw14097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14097 raw14097Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw14097 raw14097Labels = mixedMoment B raw14097step0 raw14097step0Labels := by
      have hz : ∀ j, raw14097 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14097step0 = (fun i j => raw14097 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14097step0 raw14097; decide +kernel
      have hl : raw14097step0Labels = raw14097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14097 raw14097Labels permutation590 hz
    mixedMoment B raw14097step0 raw14097step0Labels = mixedMoment B raw14097step1 raw14097step1Labels := by
      have hz : ∀ j, raw14097step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14097step1 = (fun i j => raw14097step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14097step1 raw14097step0; decide +kernel
      have hl : raw14097step1Labels = raw14097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14097step0 raw14097step0Labels permutation56 hz
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw14098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14098 raw14098Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw14098 raw14098Labels = mixedMoment B raw14098step0 raw14098step0Labels := by
      have hz : ∀ j, raw14098 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14098step0 = (fun i j => raw14098 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14098step0 raw14098; decide +kernel
      have hl : raw14098step0Labels = raw14098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14098 raw14098Labels permutation265 hz
    mixedMoment B raw14098step0 raw14098step0Labels = mixedMoment B raw14098step1 raw14098step1Labels := by
      have ha : raw14098step1 = (fun i j => raw14098step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14098step1 raw14098step0; decide +kernel
      have hl : raw14098step1Labels = raw14098step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14098step0 raw14098step0Labels permutation34 permutation2
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw14099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14099 raw14099Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw14099 raw14099Labels = mixedMoment B raw14099step0 raw14099step0Labels := by
      have ha : raw14099step0 = (fun i j => raw14099 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14099step0 raw14099; decide +kernel
      have hl : raw14099step0Labels = raw14099Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14099 raw14099Labels permutation154 permutation2
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw14100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14100 raw14100Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw14100 raw14100Labels = mixedMoment B raw14100step0 raw14100step0Labels := by
      have hz : ∀ j, raw14100 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14100step0 = (fun i j => raw14100 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14100step0 raw14100; decide +kernel
      have hl : raw14100step0Labels = raw14100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14100 raw14100Labels permutation265 hz
    mixedMoment B raw14100step0 raw14100step0Labels = mixedMoment B raw14100step1 raw14100step1Labels := by
      have ha : raw14100step1 = (fun i j => raw14100step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14100step1 raw14100step0; decide +kernel
      have hl : raw14100step1Labels = raw14100step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14100step0 raw14100step0Labels permutation34 permutation2
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw14101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14101 raw14101Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw14101 raw14101Labels = mixedMoment B raw14101step0 raw14101step0Labels := by
      have hz : ∀ j, raw14101 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14101step0 = (fun i j => raw14101 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14101step0 raw14101; decide +kernel
      have hl : raw14101step0Labels = raw14101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14101 raw14101Labels permutation265 hz
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw14102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14102 raw14102Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw14102 raw14102Labels = mixedMoment B raw14102step0 raw14102step0Labels := by
      have hz : ∀ j, raw14102 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14102step0 = (fun i j => raw14102 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14102step0 raw14102; decide +kernel
      have hl : raw14102step0Labels = raw14102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14102 raw14102Labels permutation265 hz
    mixedMoment B raw14102step0 raw14102step0Labels = mixedMoment B raw14102step1 raw14102step1Labels := by
      have ha : raw14102step1 = (fun i j => raw14102step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14102step1 raw14102step0; decide +kernel
      have hl : raw14102step1Labels = raw14102step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14102step0 raw14102step0Labels permutation34 permutation2
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw14103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14103step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14103step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14103 raw14103Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw14103 raw14103Labels = mixedMoment B raw14103step0 raw14103step0Labels := by
      have ha : raw14103step0 = (fun i j => raw14103 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14103step0 raw14103; decide +kernel
      have hl : raw14103step0Labels = raw14103Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14103 raw14103Labels permutation181 permutation7
    mixedMoment B raw14103step0 raw14103step0Labels = mixedMoment B raw14103step1 raw14103step1Labels := by
      have ha : raw14103step1 = -raw14103step0 := by apply Matrix.ext; change ∀ i j, raw14103step1 i j = -(raw14103step0 i j); unfold raw14103step1 raw14103step0; decide +kernel
      have hl : raw14103step1Labels = raw14103step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14103step1 raw14103step1Labels = mixedMoment B raw14103step2 raw14103step2Labels := by
      have ha : raw14103step2 = raw14103step1 := by apply Matrix.ext; unfold raw14103step2 raw14103step1; decide +kernel
      have hl : raw14103step1Labels = labelEmbedding1 ∘ raw14103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14103step1 raw14103step1Labels raw14103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw14104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14104step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14104step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14104step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14104step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14104 raw14104Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw14104 raw14104Labels = mixedMoment B raw14104step0 raw14104step0Labels := by
      have hz : ∀ j, raw14104 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14104step0 = (fun i j => raw14104 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14104step0 raw14104; decide +kernel
      have hl : raw14104step0Labels = raw14104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14104 raw14104Labels permutation265 hz
    mixedMoment B raw14104step0 raw14104step0Labels = mixedMoment B raw14104step1 raw14104step1Labels := by
      have ha : raw14104step1 = (fun i j => raw14104step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14104step1 raw14104step0; decide +kernel
      have hl : raw14104step1Labels = raw14104step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14104step0 raw14104step0Labels permutation37 permutation7
    mixedMoment B raw14104step1 raw14104step1Labels = mixedMoment B raw14104step2 raw14104step2Labels := by
      have ha : raw14104step2 = -raw14104step1 := by apply Matrix.ext; change ∀ i j, raw14104step2 i j = -(raw14104step1 i j); unfold raw14104step2 raw14104step1; decide +kernel
      have hl : raw14104step2Labels = raw14104step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14104step2 raw14104step2Labels = mixedMoment B raw14104step3 raw14104step3Labels := by
      have ha : raw14104step3 = raw14104step2 := by apply Matrix.ext; unfold raw14104step3 raw14104step2; decide +kernel
      have hl : raw14104step2Labels = labelEmbedding1 ∘ raw14104step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14104step2 raw14104step2Labels raw14104step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw14105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14105step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14105step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14105step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14105step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14105step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14105 raw14105Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw14105 raw14105Labels = mixedMoment B raw14105step0 raw14105step0Labels := by
      have hz : ∀ j, raw14105 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14105step0 = (fun i j => raw14105 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14105step0 raw14105; decide +kernel
      have hl : raw14105step0Labels = raw14105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14105 raw14105Labels permutation265 hz
    mixedMoment B raw14105step0 raw14105step0Labels = mixedMoment B raw14105step1 raw14105step1Labels := by
      have ha : raw14105step1 = (fun i j => raw14105step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14105step1 raw14105step0; decide +kernel
      have hl : raw14105step1Labels = raw14105step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14105step0 raw14105step0Labels permutation37 permutation7
    mixedMoment B raw14105step1 raw14105step1Labels = mixedMoment B raw14105step2 raw14105step2Labels := by
      have ha : raw14105step2 = -raw14105step1 := by apply Matrix.ext; change ∀ i j, raw14105step2 i j = -(raw14105step1 i j); unfold raw14105step2 raw14105step1; decide +kernel
      have hl : raw14105step2Labels = raw14105step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14105step2 raw14105step2Labels = mixedMoment B raw14105step3 raw14105step3Labels := by
      have ha : raw14105step3 = raw14105step2 := by apply Matrix.ext; unfold raw14105step3 raw14105step2; decide +kernel
      have hl : raw14105step2Labels = labelEmbedding1 ∘ raw14105step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14105step2 raw14105step2Labels raw14105step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw14106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14106step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14106step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14106 raw14106Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw14106 raw14106Labels = mixedMoment B raw14106step0 raw14106step0Labels := by
      have hz : ∀ j, raw14106 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14106step0 = (fun i j => raw14106 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14106step0 raw14106; decide +kernel
      have hl : raw14106step0Labels = raw14106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14106 raw14106Labels permutation265 hz
    mixedMoment B raw14106step0 raw14106step0Labels = mixedMoment B raw14106step1 raw14106step1Labels := by
      have ha : raw14106step1 = (fun i j => raw14106step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14106step1 raw14106step0; decide +kernel
      have hl : raw14106step1Labels = raw14106step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14106step0 raw14106step0Labels permutation37 permutation7
    mixedMoment B raw14106step1 raw14106step1Labels = mixedMoment B raw14106step2 raw14106step2Labels := by
      have ha : raw14106step2 = -raw14106step1 := by apply Matrix.ext; change ∀ i j, raw14106step2 i j = -(raw14106step1 i j); unfold raw14106step2 raw14106step1; decide +kernel
      have hl : raw14106step2Labels = raw14106step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14106step2 raw14106step2Labels = mixedMoment B raw14106step3 raw14106step3Labels := by
      have ha : raw14106step3 = raw14106step2 := by apply Matrix.ext; unfold raw14106step3 raw14106step2; decide +kernel
      have hl : raw14106step2Labels = labelEmbedding1 ∘ raw14106step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14106step2 raw14106step2Labels raw14106step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw14107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14107step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14107step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14107step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14107step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14107step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14107step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14107step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14107 raw14107Labels = mixedMoment B node3861 node3861Labels := by
  calc
    mixedMoment B raw14107 raw14107Labels = mixedMoment B raw14107step0 raw14107step0Labels := by
      have hz : ∀ j, raw14107 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14107step0 = (fun i j => raw14107 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14107step0 raw14107; decide +kernel
      have hl : raw14107step0Labels = raw14107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14107 raw14107Labels permutation590 hz
    mixedMoment B raw14107step0 raw14107step0Labels = mixedMoment B raw14107step1 raw14107step1Labels := by
      have hz : ∀ j, raw14107step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14107step1 = (fun i j => raw14107step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14107step1 raw14107step0; decide +kernel
      have hl : raw14107step1Labels = raw14107step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14107step0 raw14107step0Labels permutation56 hz
    mixedMoment B raw14107step1 raw14107step1Labels = mixedMoment B raw14107step2 raw14107step2Labels := by
      have ha : raw14107step2 = (fun i j => raw14107step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14107step2 raw14107step1; decide +kernel
      have hl : raw14107step2Labels = raw14107step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14107step1 raw14107step1Labels permutation9 permutation7
    mixedMoment B raw14107step2 raw14107step2Labels = mixedMoment B raw14107step3 raw14107step3Labels := by
      have ha : raw14107step3 = -raw14107step2 := by apply Matrix.ext; change ∀ i j, raw14107step3 i j = -(raw14107step2 i j); unfold raw14107step3 raw14107step2; decide +kernel
      have hl : raw14107step3Labels = raw14107step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14107step3 raw14107step3Labels = mixedMoment B raw14107step4 raw14107step4Labels := by
      have ha : raw14107step4 = raw14107step3 := by apply Matrix.ext; unfold raw14107step4 raw14107step3; decide +kernel
      have hl : raw14107step3Labels = labelEmbedding1 ∘ raw14107step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14107step3 raw14107step3Labels raw14107step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3861 node3861Labels := by rfl

def raw14108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14108step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14108step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14108 raw14108Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw14108 raw14108Labels = mixedMoment B raw14108step0 raw14108step0Labels := by
      have ha : raw14108step0 = (fun i j => raw14108 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14108step0 raw14108; decide +kernel
      have hl : raw14108step0Labels = raw14108Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14108 raw14108Labels permutation181 permutation7
    mixedMoment B raw14108step0 raw14108step0Labels = mixedMoment B raw14108step1 raw14108step1Labels := by
      have ha : raw14108step1 = -raw14108step0 := by apply Matrix.ext; change ∀ i j, raw14108step1 i j = -(raw14108step0 i j); unfold raw14108step1 raw14108step0; decide +kernel
      have hl : raw14108step1Labels = raw14108step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14108step1 raw14108step1Labels = mixedMoment B raw14108step2 raw14108step2Labels := by
      have ha : raw14108step2 = raw14108step1 := by apply Matrix.ext; unfold raw14108step2 raw14108step1; decide +kernel
      have hl : raw14108step1Labels = labelEmbedding1 ∘ raw14108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14108step1 raw14108step1Labels raw14108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw14109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14109step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14109step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14109step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14109 raw14109Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw14109 raw14109Labels = mixedMoment B raw14109step0 raw14109step0Labels := by
      have ha : raw14109step0 = (fun i j => raw14109 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14109step0 raw14109; decide +kernel
      have hl : raw14109step0Labels = raw14109Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14109 raw14109Labels permutation181 permutation7
    mixedMoment B raw14109step0 raw14109step0Labels = mixedMoment B raw14109step1 raw14109step1Labels := by
      have ha : raw14109step1 = -raw14109step0 := by apply Matrix.ext; change ∀ i j, raw14109step1 i j = -(raw14109step0 i j); unfold raw14109step1 raw14109step0; decide +kernel
      have hl : raw14109step1Labels = raw14109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14109step1 raw14109step1Labels = mixedMoment B raw14109step2 raw14109step2Labels := by
      have ha : raw14109step2 = raw14109step1 := by apply Matrix.ext; unfold raw14109step2 raw14109step1; decide +kernel
      have hl : raw14109step1Labels = labelEmbedding1 ∘ raw14109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14109step1 raw14109step1Labels raw14109step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

def raw14110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14110step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14110 raw14110Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw14110 raw14110Labels = mixedMoment B raw14110step0 raw14110step0Labels := by
      have ha : raw14110step0 = (fun i j => raw14110 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14110step0 raw14110; decide +kernel
      have hl : raw14110step0Labels = raw14110Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14110 raw14110Labels permutation181 permutation7
    mixedMoment B raw14110step0 raw14110step0Labels = mixedMoment B raw14110step1 raw14110step1Labels := by
      have ha : raw14110step1 = -raw14110step0 := by apply Matrix.ext; change ∀ i j, raw14110step1 i j = -(raw14110step0 i j); unfold raw14110step1 raw14110step0; decide +kernel
      have hl : raw14110step1Labels = raw14110step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14110step1 raw14110step1Labels = mixedMoment B raw14110step2 raw14110step2Labels := by
      have ha : raw14110step2 = raw14110step1 := by apply Matrix.ext; unfold raw14110step2 raw14110step1; decide +kernel
      have hl : raw14110step1Labels = labelEmbedding1 ∘ raw14110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14110step1 raw14110step1Labels raw14110step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw14111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14111step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14111step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14111step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14111 raw14111Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw14111 raw14111Labels = mixedMoment B raw14111step0 raw14111step0Labels := by
      have ha : raw14111step0 = (fun i j => raw14111 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14111step0 raw14111; decide +kernel
      have hl : raw14111step0Labels = raw14111Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14111 raw14111Labels permutation181 permutation7
    mixedMoment B raw14111step0 raw14111step0Labels = mixedMoment B raw14111step1 raw14111step1Labels := by
      have ha : raw14111step1 = -raw14111step0 := by apply Matrix.ext; change ∀ i j, raw14111step1 i j = -(raw14111step0 i j); unfold raw14111step1 raw14111step0; decide +kernel
      have hl : raw14111step1Labels = raw14111step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14111step1 raw14111step1Labels = mixedMoment B raw14111step2 raw14111step2Labels := by
      have ha : raw14111step2 = raw14111step1 := by apply Matrix.ext; unfold raw14111step2 raw14111step1; decide +kernel
      have hl : raw14111step1Labels = labelEmbedding1 ∘ raw14111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14111step1 raw14111step1Labels raw14111step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw14112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14112step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14112step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14112step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14112step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14112 raw14112Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw14112 raw14112Labels = mixedMoment B raw14112step0 raw14112step0Labels := by
      have hz : ∀ j, raw14112 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14112step0 = (fun i j => raw14112 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14112step0 raw14112; decide +kernel
      have hl : raw14112step0Labels = raw14112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14112 raw14112Labels permutation590 hz
    mixedMoment B raw14112step0 raw14112step0Labels = mixedMoment B raw14112step1 raw14112step1Labels := by
      have ha : raw14112step1 = (fun i j => raw14112step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14112step1 raw14112step0; decide +kernel
      have hl : raw14112step1Labels = raw14112step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14112step0 raw14112step0Labels permutation39 permutation7
    mixedMoment B raw14112step1 raw14112step1Labels = mixedMoment B raw14112step2 raw14112step2Labels := by
      have ha : raw14112step2 = -raw14112step1 := by apply Matrix.ext; change ∀ i j, raw14112step2 i j = -(raw14112step1 i j); unfold raw14112step2 raw14112step1; decide +kernel
      have hl : raw14112step2Labels = raw14112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14112step2 raw14112step2Labels = mixedMoment B raw14112step3 raw14112step3Labels := by
      have ha : raw14112step3 = raw14112step2 := by apply Matrix.ext; unfold raw14112step3 raw14112step2; decide +kernel
      have hl : raw14112step2Labels = labelEmbedding1 ∘ raw14112step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14112step2 raw14112step2Labels raw14112step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw14113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14113step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14113step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14113step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14113 raw14113Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw14113 raw14113Labels = mixedMoment B raw14113step0 raw14113step0Labels := by
      have hz : ∀ j, raw14113 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14113step0 = (fun i j => raw14113 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14113step0 raw14113; decide +kernel
      have hl : raw14113step0Labels = raw14113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14113 raw14113Labels permutation265 hz
    mixedMoment B raw14113step0 raw14113step0Labels = mixedMoment B raw14113step1 raw14113step1Labels := by
      have ha : raw14113step1 = (fun i j => raw14113step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14113step1 raw14113step0; decide +kernel
      have hl : raw14113step1Labels = raw14113step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14113step0 raw14113step0Labels permutation41 permutation5
    mixedMoment B raw14113step1 raw14113step1Labels = mixedMoment B raw14113step2 raw14113step2Labels := by
      have ha : raw14113step2 = -raw14113step1 := by apply Matrix.ext; change ∀ i j, raw14113step2 i j = -(raw14113step1 i j); unfold raw14113step2 raw14113step1; decide +kernel
      have hl : raw14113step2Labels = raw14113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14113step2 raw14113step2Labels = mixedMoment B raw14113step3 raw14113step3Labels := by
      have ha : raw14113step3 = raw14113step2 := by apply Matrix.ext; unfold raw14113step3 raw14113step2; decide +kernel
      have hl : raw14113step2Labels = labelEmbedding1 ∘ raw14113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14113step2 raw14113step2Labels raw14113step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw14114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14114step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14114 raw14114Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw14114 raw14114Labels = mixedMoment B raw14114step0 raw14114step0Labels := by
      have ha : raw14114step0 = (fun i j => raw14114 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14114step0 raw14114; decide +kernel
      have hl : raw14114step0Labels = raw14114Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14114 raw14114Labels permutation181 permutation7
    mixedMoment B raw14114step0 raw14114step0Labels = mixedMoment B raw14114step1 raw14114step1Labels := by
      have ha : raw14114step1 = -raw14114step0 := by apply Matrix.ext; change ∀ i j, raw14114step1 i j = -(raw14114step0 i j); unfold raw14114step1 raw14114step0; decide +kernel
      have hl : raw14114step1Labels = raw14114step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14114step1 raw14114step1Labels = mixedMoment B raw14114step2 raw14114step2Labels := by
      have ha : raw14114step2 = raw14114step1 := by apply Matrix.ext; unfold raw14114step2 raw14114step1; decide +kernel
      have hl : raw14114step1Labels = labelEmbedding1 ∘ raw14114step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14114step1 raw14114step1Labels raw14114step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw14115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14115step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14115step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14115step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14115step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14115 raw14115Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw14115 raw14115Labels = mixedMoment B raw14115step0 raw14115step0Labels := by
      have hz : ∀ j, raw14115 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14115step0 = (fun i j => raw14115 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14115step0 raw14115; decide +kernel
      have hl : raw14115step0Labels = raw14115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14115 raw14115Labels permutation265 hz
    mixedMoment B raw14115step0 raw14115step0Labels = mixedMoment B raw14115step1 raw14115step1Labels := by
      have ha : raw14115step1 = (fun i j => raw14115step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14115step1 raw14115step0; decide +kernel
      have hl : raw14115step1Labels = raw14115step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14115step0 raw14115step0Labels permutation37 permutation7
    mixedMoment B raw14115step1 raw14115step1Labels = mixedMoment B raw14115step2 raw14115step2Labels := by
      have ha : raw14115step2 = -raw14115step1 := by apply Matrix.ext; change ∀ i j, raw14115step2 i j = -(raw14115step1 i j); unfold raw14115step2 raw14115step1; decide +kernel
      have hl : raw14115step2Labels = raw14115step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14115step2 raw14115step2Labels = mixedMoment B raw14115step3 raw14115step3Labels := by
      have ha : raw14115step3 = raw14115step2 := by apply Matrix.ext; unfold raw14115step3 raw14115step2; decide +kernel
      have hl : raw14115step2Labels = labelEmbedding1 ∘ raw14115step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14115step2 raw14115step2Labels raw14115step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw14116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14116step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14116step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14116step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14116step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14116 raw14116Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw14116 raw14116Labels = mixedMoment B raw14116step0 raw14116step0Labels := by
      have hz : ∀ j, raw14116 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14116step0 = (fun i j => raw14116 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14116step0 raw14116; decide +kernel
      have hl : raw14116step0Labels = raw14116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14116 raw14116Labels permutation265 hz
    mixedMoment B raw14116step0 raw14116step0Labels = mixedMoment B raw14116step1 raw14116step1Labels := by
      have ha : raw14116step1 = (fun i j => raw14116step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14116step1 raw14116step0; decide +kernel
      have hl : raw14116step1Labels = raw14116step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14116step0 raw14116step0Labels permutation37 permutation7
    mixedMoment B raw14116step1 raw14116step1Labels = mixedMoment B raw14116step2 raw14116step2Labels := by
      have ha : raw14116step2 = -raw14116step1 := by apply Matrix.ext; change ∀ i j, raw14116step2 i j = -(raw14116step1 i j); unfold raw14116step2 raw14116step1; decide +kernel
      have hl : raw14116step2Labels = raw14116step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14116step2 raw14116step2Labels = mixedMoment B raw14116step3 raw14116step3Labels := by
      have ha : raw14116step3 = raw14116step2 := by apply Matrix.ext; unfold raw14116step3 raw14116step2; decide +kernel
      have hl : raw14116step2Labels = labelEmbedding1 ∘ raw14116step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14116step2 raw14116step2Labels raw14116step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw14117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14117step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw14117step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14117step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14117step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14117step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14117step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14117 raw14117Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw14117 raw14117Labels = mixedMoment B raw14117step0 raw14117step0Labels := by
      have hz : ∀ j, raw14117 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14117step0 = (fun i j => raw14117 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14117step0 raw14117; decide +kernel
      have hl : raw14117step0Labels = raw14117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14117 raw14117Labels permutation590 hz
    mixedMoment B raw14117step0 raw14117step0Labels = mixedMoment B raw14117step1 raw14117step1Labels := by
      have hz : ∀ j, raw14117step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14117step1 = (fun i j => raw14117step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14117step1 raw14117step0; decide +kernel
      have hl : raw14117step1Labels = raw14117step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14117step0 raw14117step0Labels permutation56 hz
    mixedMoment B raw14117step1 raw14117step1Labels = mixedMoment B raw14117step2 raw14117step2Labels := by
      have ha : raw14117step2 = (fun i j => raw14117step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14117step2 raw14117step1; decide +kernel
      have hl : raw14117step2Labels = raw14117step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14117step1 raw14117step1Labels permutation9 permutation7
    mixedMoment B raw14117step2 raw14117step2Labels = mixedMoment B raw14117step3 raw14117step3Labels := by
      have ha : raw14117step3 = -raw14117step2 := by apply Matrix.ext; change ∀ i j, raw14117step3 i j = -(raw14117step2 i j); unfold raw14117step3 raw14117step2; decide +kernel
      have hl : raw14117step3Labels = raw14117step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14117step3 raw14117step3Labels = mixedMoment B raw14117step4 raw14117step4Labels := by
      have ha : raw14117step4 = raw14117step3 := by apply Matrix.ext; unfold raw14117step4 raw14117step3; decide +kernel
      have hl : raw14117step3Labels = labelEmbedding1 ∘ raw14117step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14117step3 raw14117step3Labels raw14117step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw14118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14118step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw14118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14118step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14118step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14118step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14118 raw14118Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw14118 raw14118Labels = mixedMoment B raw14118step0 raw14118step0Labels := by
      have hz : ∀ j, raw14118 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14118step0 = (fun i j => raw14118 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14118step0 raw14118; decide +kernel
      have hl : raw14118step0Labels = raw14118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14118 raw14118Labels permutation265 hz
    mixedMoment B raw14118step0 raw14118step0Labels = mixedMoment B raw14118step1 raw14118step1Labels := by
      have ha : raw14118step1 = (fun i j => raw14118step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14118step1 raw14118step0; decide +kernel
      have hl : raw14118step1Labels = raw14118step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14118step0 raw14118step0Labels permutation37 permutation7
    mixedMoment B raw14118step1 raw14118step1Labels = mixedMoment B raw14118step2 raw14118step2Labels := by
      have ha : raw14118step2 = -raw14118step1 := by apply Matrix.ext; change ∀ i j, raw14118step2 i j = -(raw14118step1 i j); unfold raw14118step2 raw14118step1; decide +kernel
      have hl : raw14118step2Labels = raw14118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14118step2 raw14118step2Labels = mixedMoment B raw14118step3 raw14118step3Labels := by
      have ha : raw14118step3 = raw14118step2 := by apply Matrix.ext; unfold raw14118step3 raw14118step2; decide +kernel
      have hl : raw14118step2Labels = labelEmbedding1 ∘ raw14118step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14118step2 raw14118step2Labels raw14118step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw14119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw14119step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14119step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14119step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14119step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14119 raw14119Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw14119 raw14119Labels = mixedMoment B raw14119step0 raw14119step0Labels := by
      have ha : raw14119step0 = (fun i j => raw14119 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14119step0 raw14119; decide +kernel
      have hl : raw14119step0Labels = raw14119Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14119 raw14119Labels permutation181 permutation7
    mixedMoment B raw14119step0 raw14119step0Labels = mixedMoment B raw14119step1 raw14119step1Labels := by
      have ha : raw14119step1 = -raw14119step0 := by apply Matrix.ext; change ∀ i j, raw14119step1 i j = -(raw14119step0 i j); unfold raw14119step1 raw14119step0; decide +kernel
      have hl : raw14119step1Labels = raw14119step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14119step1 raw14119step1Labels = mixedMoment B raw14119step2 raw14119step2Labels := by
      have ha : raw14119step2 = raw14119step1 := by apply Matrix.ext; unfold raw14119step2 raw14119step1; decide +kernel
      have hl : raw14119step1Labels = labelEmbedding1 ∘ raw14119step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14119step1 raw14119step1Labels raw14119step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw14120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw14120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14120step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14120step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14120step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14120 raw14120Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw14120 raw14120Labels = mixedMoment B raw14120step0 raw14120step0Labels := by
      have hz : ∀ j, raw14120 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14120step0 = (fun i j => raw14120 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14120step0 raw14120; decide +kernel
      have hl : raw14120step0Labels = raw14120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14120 raw14120Labels permutation265 hz
    mixedMoment B raw14120step0 raw14120step0Labels = mixedMoment B raw14120step1 raw14120step1Labels := by
      have ha : raw14120step1 = (fun i j => raw14120step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14120step1 raw14120step0; decide +kernel
      have hl : raw14120step1Labels = raw14120step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14120step0 raw14120step0Labels permutation37 permutation7
    mixedMoment B raw14120step1 raw14120step1Labels = mixedMoment B raw14120step2 raw14120step2Labels := by
      have ha : raw14120step2 = -raw14120step1 := by apply Matrix.ext; change ∀ i j, raw14120step2 i j = -(raw14120step1 i j); unfold raw14120step2 raw14120step1; decide +kernel
      have hl : raw14120step2Labels = raw14120step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14120step2 raw14120step2Labels = mixedMoment B raw14120step3 raw14120step3Labels := by
      have ha : raw14120step3 = raw14120step2 := by apply Matrix.ext; unfold raw14120step3 raw14120step2; decide +kernel
      have hl : raw14120step2Labels = labelEmbedding1 ∘ raw14120step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14120step2 raw14120step2Labels raw14120step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

def raw14121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw14121step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14121step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14121step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14121step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14121step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14121 raw14121Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw14121 raw14121Labels = mixedMoment B raw14121step0 raw14121step0Labels := by
      have hz : ∀ j, raw14121 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14121step0 = (fun i j => raw14121 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14121step0 raw14121; decide +kernel
      have hl : raw14121step0Labels = raw14121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14121 raw14121Labels permutation265 hz
    mixedMoment B raw14121step0 raw14121step0Labels = mixedMoment B raw14121step1 raw14121step1Labels := by
      have ha : raw14121step1 = (fun i j => raw14121step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14121step1 raw14121step0; decide +kernel
      have hl : raw14121step1Labels = raw14121step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14121step0 raw14121step0Labels permutation37 permutation7
    mixedMoment B raw14121step1 raw14121step1Labels = mixedMoment B raw14121step2 raw14121step2Labels := by
      have ha : raw14121step2 = -raw14121step1 := by apply Matrix.ext; change ∀ i j, raw14121step2 i j = -(raw14121step1 i j); unfold raw14121step2 raw14121step1; decide +kernel
      have hl : raw14121step2Labels = raw14121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14121step2 raw14121step2Labels = mixedMoment B raw14121step3 raw14121step3Labels := by
      have ha : raw14121step3 = raw14121step2 := by apply Matrix.ext; unfold raw14121step3 raw14121step2; decide +kernel
      have hl : raw14121step2Labels = labelEmbedding1 ∘ raw14121step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14121step2 raw14121step2Labels raw14121step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw14122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw14122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw14122step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw14122step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14122step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14122step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14122step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14122step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14122step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14122step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14122 raw14122Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw14122 raw14122Labels = mixedMoment B raw14122step0 raw14122step0Labels := by
      have hz : ∀ j, raw14122 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14122step0 = (fun i j => raw14122 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14122step0 raw14122; decide +kernel
      have hl : raw14122step0Labels = raw14122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14122 raw14122Labels permutation590 hz
    mixedMoment B raw14122step0 raw14122step0Labels = mixedMoment B raw14122step1 raw14122step1Labels := by
      have hz : ∀ j, raw14122step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14122step1 = (fun i j => raw14122step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14122step1 raw14122step0; decide +kernel
      have hl : raw14122step1Labels = raw14122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14122step0 raw14122step0Labels permutation56 hz
    mixedMoment B raw14122step1 raw14122step1Labels = mixedMoment B raw14122step2 raw14122step2Labels := by
      have ha : raw14122step2 = (fun i j => raw14122step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14122step2 raw14122step1; decide +kernel
      have hl : raw14122step2Labels = raw14122step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14122step1 raw14122step1Labels permutation9 permutation7
    mixedMoment B raw14122step2 raw14122step2Labels = mixedMoment B raw14122step3 raw14122step3Labels := by
      have ha : raw14122step3 = -raw14122step2 := by apply Matrix.ext; change ∀ i j, raw14122step3 i j = -(raw14122step2 i j); unfold raw14122step3 raw14122step2; decide +kernel
      have hl : raw14122step3Labels = raw14122step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14122step3 raw14122step3Labels = mixedMoment B raw14122step4 raw14122step4Labels := by
      have ha : raw14122step4 = raw14122step3 := by apply Matrix.ext; unfold raw14122step4 raw14122step3; decide +kernel
      have hl : raw14122step3Labels = labelEmbedding1 ∘ raw14122step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14122step3 raw14122step3Labels raw14122step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw14123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14123Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14123step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14123step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14123step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14123step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14123 raw14123Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw14123 raw14123Labels = mixedMoment B raw14123step0 raw14123step0Labels := by
      have hz : ∀ j, raw14123 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14123step0 = (fun i j => raw14123 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14123step0 raw14123; decide +kernel
      have hl : raw14123step0Labels = raw14123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14123 raw14123Labels permutation265 hz
    mixedMoment B raw14123step0 raw14123step0Labels = mixedMoment B raw14123step1 raw14123step1Labels := by
      have ha : raw14123step1 = (fun i j => raw14123step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14123step1 raw14123step0; decide +kernel
      have hl : raw14123step1Labels = raw14123step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14123step0 raw14123step0Labels permutation37 permutation7
    mixedMoment B raw14123step1 raw14123step1Labels = mixedMoment B raw14123step2 raw14123step2Labels := by
      have ha : raw14123step2 = -raw14123step1 := by apply Matrix.ext; change ∀ i j, raw14123step2 i j = -(raw14123step1 i j); unfold raw14123step2 raw14123step1; decide +kernel
      have hl : raw14123step2Labels = raw14123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14123step2 raw14123step2Labels = mixedMoment B raw14123step3 raw14123step3Labels := by
      have ha : raw14123step3 = raw14123step2 := by apply Matrix.ext; unfold raw14123step3 raw14123step2; decide +kernel
      have hl : raw14123step2Labels = labelEmbedding1 ∘ raw14123step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14123step2 raw14123step2Labels raw14123step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw14124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14124step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14124step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14124step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14124 raw14124Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw14124 raw14124Labels = mixedMoment B raw14124step0 raw14124step0Labels := by
      have ha : raw14124step0 = (fun i j => raw14124 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14124step0 raw14124; decide +kernel
      have hl : raw14124step0Labels = raw14124Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14124 raw14124Labels permutation181 permutation7
    mixedMoment B raw14124step0 raw14124step0Labels = mixedMoment B raw14124step1 raw14124step1Labels := by
      have ha : raw14124step1 = -raw14124step0 := by apply Matrix.ext; change ∀ i j, raw14124step1 i j = -(raw14124step0 i j); unfold raw14124step1 raw14124step0; decide +kernel
      have hl : raw14124step1Labels = raw14124step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14124step1 raw14124step1Labels = mixedMoment B raw14124step2 raw14124step2Labels := by
      have ha : raw14124step2 = raw14124step1 := by apply Matrix.ext; unfold raw14124step2 raw14124step1; decide +kernel
      have hl : raw14124step1Labels = labelEmbedding1 ∘ raw14124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14124step1 raw14124step1Labels raw14124step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3515 node3515Labels := by rfl

def raw14125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14125Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14125step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14125step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14125step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14125step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14125step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14125 raw14125Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw14125 raw14125Labels = mixedMoment B raw14125step0 raw14125step0Labels := by
      have hz : ∀ j, raw14125 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14125step0 = (fun i j => raw14125 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14125step0 raw14125; decide +kernel
      have hl : raw14125step0Labels = raw14125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14125 raw14125Labels permutation265 hz
    mixedMoment B raw14125step0 raw14125step0Labels = mixedMoment B raw14125step1 raw14125step1Labels := by
      have ha : raw14125step1 = (fun i j => raw14125step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14125step1 raw14125step0; decide +kernel
      have hl : raw14125step1Labels = raw14125step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14125step0 raw14125step0Labels permutation37 permutation7
    mixedMoment B raw14125step1 raw14125step1Labels = mixedMoment B raw14125step2 raw14125step2Labels := by
      have ha : raw14125step2 = -raw14125step1 := by apply Matrix.ext; change ∀ i j, raw14125step2 i j = -(raw14125step1 i j); unfold raw14125step2 raw14125step1; decide +kernel
      have hl : raw14125step2Labels = raw14125step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14125step2 raw14125step2Labels = mixedMoment B raw14125step3 raw14125step3Labels := by
      have ha : raw14125step3 = raw14125step2 := by apply Matrix.ext; unfold raw14125step3 raw14125step2; decide +kernel
      have hl : raw14125step2Labels = labelEmbedding1 ∘ raw14125step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14125step2 raw14125step2Labels raw14125step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw14126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14126step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14126step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14126step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14126 raw14126Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw14126 raw14126Labels = mixedMoment B raw14126step0 raw14126step0Labels := by
      have hz : ∀ j, raw14126 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14126step0 = (fun i j => raw14126 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14126step0 raw14126; decide +kernel
      have hl : raw14126step0Labels = raw14126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14126 raw14126Labels permutation265 hz
    mixedMoment B raw14126step0 raw14126step0Labels = mixedMoment B raw14126step1 raw14126step1Labels := by
      have ha : raw14126step1 = (fun i j => raw14126step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14126step1 raw14126step0; decide +kernel
      have hl : raw14126step1Labels = raw14126step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14126step0 raw14126step0Labels permutation37 permutation7
    mixedMoment B raw14126step1 raw14126step1Labels = mixedMoment B raw14126step2 raw14126step2Labels := by
      have ha : raw14126step2 = -raw14126step1 := by apply Matrix.ext; change ∀ i j, raw14126step2 i j = -(raw14126step1 i j); unfold raw14126step2 raw14126step1; decide +kernel
      have hl : raw14126step2Labels = raw14126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14126step2 raw14126step2Labels = mixedMoment B raw14126step3 raw14126step3Labels := by
      have ha : raw14126step3 = raw14126step2 := by apply Matrix.ext; unfold raw14126step3 raw14126step2; decide +kernel
      have hl : raw14126step2Labels = labelEmbedding1 ∘ raw14126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14126step2 raw14126step2Labels raw14126step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw14127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw14127Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14127step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14127step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw14127step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14127step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14127step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw14127step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14127 raw14127Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw14127 raw14127Labels = mixedMoment B raw14127step0 raw14127step0Labels := by
      have hz : ∀ j, raw14127 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14127step0 = (fun i j => raw14127 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14127step0 raw14127; decide +kernel
      have hl : raw14127step0Labels = raw14127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14127 raw14127Labels permutation590 hz
    mixedMoment B raw14127step0 raw14127step0Labels = mixedMoment B raw14127step1 raw14127step1Labels := by
      have hz : ∀ j, raw14127step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14127step1 = (fun i j => raw14127step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14127step1 raw14127step0; decide +kernel
      have hl : raw14127step1Labels = raw14127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14127step0 raw14127step0Labels permutation56 hz
    mixedMoment B raw14127step1 raw14127step1Labels = mixedMoment B raw14127step2 raw14127step2Labels := by
      have ha : raw14127step2 = (fun i j => raw14127step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14127step2 raw14127step1; decide +kernel
      have hl : raw14127step2Labels = raw14127step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14127step1 raw14127step1Labels permutation9 permutation7
    mixedMoment B raw14127step2 raw14127step2Labels = mixedMoment B raw14127step3 raw14127step3Labels := by
      have ha : raw14127step3 = -raw14127step2 := by apply Matrix.ext; change ∀ i j, raw14127step3 i j = -(raw14127step2 i j); unfold raw14127step3 raw14127step2; decide +kernel
      have hl : raw14127step3Labels = raw14127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14127step3 raw14127step3Labels = mixedMoment B raw14127step4 raw14127step4Labels := by
      have ha : raw14127step4 = raw14127step3 := by apply Matrix.ext; unfold raw14127step4 raw14127step3; decide +kernel
      have hl : raw14127step3Labels = labelEmbedding1 ∘ raw14127step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14127step3 raw14127step3Labels raw14127step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw14128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14128step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14128step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14128 raw14128Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw14128 raw14128Labels = mixedMoment B raw14128step0 raw14128step0Labels := by
      have hz : ∀ j, raw14128 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14128step0 = (fun i j => raw14128 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14128step0 raw14128; decide +kernel
      have hl : raw14128step0Labels = raw14128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14128 raw14128Labels permutation265 hz
    mixedMoment B raw14128step0 raw14128step0Labels = mixedMoment B raw14128step1 raw14128step1Labels := by
      have ha : raw14128step1 = (fun i j => raw14128step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14128step1 raw14128step0; decide +kernel
      have hl : raw14128step1Labels = raw14128step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14128step0 raw14128step0Labels permutation37 permutation7
    mixedMoment B raw14128step1 raw14128step1Labels = mixedMoment B raw14128step2 raw14128step2Labels := by
      have ha : raw14128step2 = -raw14128step1 := by apply Matrix.ext; change ∀ i j, raw14128step2 i j = -(raw14128step1 i j); unfold raw14128step2 raw14128step1; decide +kernel
      have hl : raw14128step2Labels = raw14128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14128step2 raw14128step2Labels = mixedMoment B raw14128step3 raw14128step3Labels := by
      have ha : raw14128step3 = raw14128step2 := by apply Matrix.ext; unfold raw14128step3 raw14128step2; decide +kernel
      have hl : raw14128step2Labels = labelEmbedding1 ∘ raw14128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14128step2 raw14128step2Labels raw14128step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw14129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14129step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14129step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14129step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14129step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14129step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14129 raw14129Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw14129 raw14129Labels = mixedMoment B raw14129step0 raw14129step0Labels := by
      have ha : raw14129step0 = (fun i j => raw14129 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14129step0 raw14129; decide +kernel
      have hl : raw14129step0Labels = raw14129Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14129 raw14129Labels permutation181 permutation7
    mixedMoment B raw14129step0 raw14129step0Labels = mixedMoment B raw14129step1 raw14129step1Labels := by
      have ha : raw14129step1 = -raw14129step0 := by apply Matrix.ext; change ∀ i j, raw14129step1 i j = -(raw14129step0 i j); unfold raw14129step1 raw14129step0; decide +kernel
      have hl : raw14129step1Labels = raw14129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14129step1 raw14129step1Labels = mixedMoment B raw14129step2 raw14129step2Labels := by
      have ha : raw14129step2 = raw14129step1 := by apply Matrix.ext; unfold raw14129step2 raw14129step1; decide +kernel
      have hl : raw14129step1Labels = labelEmbedding1 ∘ raw14129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14129step1 raw14129step1Labels raw14129step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw14130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14130step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw14130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14130step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw14130step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14130 raw14130Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw14130 raw14130Labels = mixedMoment B raw14130step0 raw14130step0Labels := by
      have hz : ∀ j, raw14130 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14130step0 = (fun i j => raw14130 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14130step0 raw14130; decide +kernel
      have hl : raw14130step0Labels = raw14130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14130 raw14130Labels permutation265 hz
    mixedMoment B raw14130step0 raw14130step0Labels = mixedMoment B raw14130step1 raw14130step1Labels := by
      have ha : raw14130step1 = (fun i j => raw14130step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14130step1 raw14130step0; decide +kernel
      have hl : raw14130step1Labels = raw14130step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14130step0 raw14130step0Labels permutation37 permutation7
    mixedMoment B raw14130step1 raw14130step1Labels = mixedMoment B raw14130step2 raw14130step2Labels := by
      have ha : raw14130step2 = -raw14130step1 := by apply Matrix.ext; change ∀ i j, raw14130step2 i j = -(raw14130step1 i j); unfold raw14130step2 raw14130step1; decide +kernel
      have hl : raw14130step2Labels = raw14130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14130step2 raw14130step2Labels = mixedMoment B raw14130step3 raw14130step3Labels := by
      have ha : raw14130step3 = raw14130step2 := by apply Matrix.ext; unfold raw14130step3 raw14130step2; decide +kernel
      have hl : raw14130step2Labels = labelEmbedding1 ∘ raw14130step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14130step2 raw14130step2Labels raw14130step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

def raw14131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14131step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14131step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14131step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14131step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14131 raw14131Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw14131 raw14131Labels = mixedMoment B raw14131step0 raw14131step0Labels := by
      have hz : ∀ j, raw14131 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14131step0 = (fun i j => raw14131 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14131step0 raw14131; decide +kernel
      have hl : raw14131step0Labels = raw14131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14131 raw14131Labels permutation265 hz
    mixedMoment B raw14131step0 raw14131step0Labels = mixedMoment B raw14131step1 raw14131step1Labels := by
      have ha : raw14131step1 = (fun i j => raw14131step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14131step1 raw14131step0; decide +kernel
      have hl : raw14131step1Labels = raw14131step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14131step0 raw14131step0Labels permutation37 permutation7
    mixedMoment B raw14131step1 raw14131step1Labels = mixedMoment B raw14131step2 raw14131step2Labels := by
      have ha : raw14131step2 = -raw14131step1 := by apply Matrix.ext; change ∀ i j, raw14131step2 i j = -(raw14131step1 i j); unfold raw14131step2 raw14131step1; decide +kernel
      have hl : raw14131step2Labels = raw14131step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14131step2 raw14131step2Labels = mixedMoment B raw14131step3 raw14131step3Labels := by
      have ha : raw14131step3 = raw14131step2 := by apply Matrix.ext; unfold raw14131step3 raw14131step2; decide +kernel
      have hl : raw14131step2Labels = labelEmbedding1 ∘ raw14131step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14131step2 raw14131step2Labels raw14131step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw14132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14132step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14132step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14132step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14132step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14132 raw14132Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw14132 raw14132Labels = mixedMoment B raw14132step0 raw14132step0Labels := by
      have hz : ∀ j, raw14132 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14132step0 = (fun i j => raw14132 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14132step0 raw14132; decide +kernel
      have hl : raw14132step0Labels = raw14132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14132 raw14132Labels permutation265 hz
    mixedMoment B raw14132step0 raw14132step0Labels = mixedMoment B raw14132step1 raw14132step1Labels := by
      have ha : raw14132step1 = (fun i j => raw14132step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14132step1 raw14132step0; decide +kernel
      have hl : raw14132step1Labels = raw14132step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14132step0 raw14132step0Labels permutation37 permutation7
    mixedMoment B raw14132step1 raw14132step1Labels = mixedMoment B raw14132step2 raw14132step2Labels := by
      have ha : raw14132step2 = -raw14132step1 := by apply Matrix.ext; change ∀ i j, raw14132step2 i j = -(raw14132step1 i j); unfold raw14132step2 raw14132step1; decide +kernel
      have hl : raw14132step2Labels = raw14132step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14132step2 raw14132step2Labels = mixedMoment B raw14132step3 raw14132step3Labels := by
      have ha : raw14132step3 = raw14132step2 := by apply Matrix.ext; unfold raw14132step3 raw14132step2; decide +kernel
      have hl : raw14132step2Labels = labelEmbedding1 ∘ raw14132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14132step2 raw14132step2Labels raw14132step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw14133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14133step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14133 raw14133Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw14133 raw14133Labels = mixedMoment B raw14133step0 raw14133step0Labels := by
      have ha : raw14133step0 = (fun i j => raw14133 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14133step0 raw14133; decide +kernel
      have hl : raw14133step0Labels = raw14133Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14133 raw14133Labels permutation157 permutation3
    mixedMoment B raw14133step0 raw14133step0Labels = mixedMoment B raw14133step1 raw14133step1Labels := by
      have ha : raw14133step1 = raw14133step0 := by apply Matrix.ext; unfold raw14133step1 raw14133step0; decide +kernel
      have hl : raw14133step0Labels = labelEmbedding6 ∘ raw14133step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14133step0 raw14133step0Labels raw14133step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw14134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14134step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14134step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14134step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14134step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14134 raw14134Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw14134 raw14134Labels = mixedMoment B raw14134step0 raw14134step0Labels := by
      have hz : ∀ j, raw14134 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14134step0 = (fun i j => raw14134 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14134step0 raw14134; decide +kernel
      have hl : raw14134step0Labels = raw14134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14134 raw14134Labels permutation265 hz
    mixedMoment B raw14134step0 raw14134step0Labels = mixedMoment B raw14134step1 raw14134step1Labels := by
      have ha : raw14134step1 = (fun i j => raw14134step0 (permutation61 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14134step1 raw14134step0; decide +kernel
      have hl : raw14134step1Labels = raw14134step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14134step0 raw14134step0Labels permutation61 permutation5
    mixedMoment B raw14134step1 raw14134step1Labels = mixedMoment B raw14134step2 raw14134step2Labels := by
      have ha : raw14134step2 = -raw14134step1 := by apply Matrix.ext; change ∀ i j, raw14134step2 i j = -(raw14134step1 i j); unfold raw14134step2 raw14134step1; decide +kernel
      have hl : raw14134step2Labels = raw14134step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14134step2 raw14134step2Labels = mixedMoment B raw14134step3 raw14134step3Labels := by
      have ha : raw14134step3 = raw14134step2 := by apply Matrix.ext; unfold raw14134step3 raw14134step2; decide +kernel
      have hl : raw14134step2Labels = labelEmbedding8 ∘ raw14134step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14134step2 raw14134step2Labels raw14134step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw14135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw14135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14135 raw14135Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw14135 raw14135Labels = mixedMoment B raw14135step0 raw14135step0Labels := by
      have hz : ∀ j, raw14135 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14135step0 = (fun i j => raw14135 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14135step0 raw14135; decide +kernel
      have hl : raw14135step0Labels = raw14135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14135 raw14135Labels permutation265 hz
    mixedMoment B raw14135step0 raw14135step0Labels = mixedMoment B raw14135step1 raw14135step1Labels := by
      have ha : raw14135step1 = (fun i j => raw14135step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14135step1 raw14135step0; decide +kernel
      have hl : raw14135step1Labels = raw14135step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14135step0 raw14135step0Labels permutation38 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw14136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14136step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14136step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14136step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14136step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14136 raw14136Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw14136 raw14136Labels = mixedMoment B raw14136step0 raw14136step0Labels := by
      have hz : ∀ j, raw14136 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14136step0 = (fun i j => raw14136 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14136step0 raw14136; decide +kernel
      have hl : raw14136step0Labels = raw14136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14136 raw14136Labels permutation520 hz
    mixedMoment B raw14136step0 raw14136step0Labels = mixedMoment B raw14136step1 raw14136step1Labels := by
      have hz : ∀ j, raw14136step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14136step1 = (fun i j => raw14136step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14136step1 raw14136step0; decide +kernel
      have hl : raw14136step1Labels = raw14136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14136step0 raw14136step0Labels permutation56 hz
    mixedMoment B raw14136step1 raw14136step1Labels = mixedMoment B raw14136step2 raw14136step2Labels := by
      have ha : raw14136step2 = (fun i j => raw14136step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14136step2 raw14136step1; decide +kernel
      have hl : raw14136step2Labels = raw14136step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14136step1 raw14136step1Labels permutation9 permutation3
    mixedMoment B raw14136step2 raw14136step2Labels = mixedMoment B raw14136step3 raw14136step3Labels := by
      have ha : raw14136step3 = raw14136step2 := by apply Matrix.ext; unfold raw14136step3 raw14136step2; decide +kernel
      have hl : raw14136step2Labels = labelEmbedding6 ∘ raw14136step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14136step2 raw14136step2Labels raw14136step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw14137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14137step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14137step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14137 raw14137Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw14137 raw14137Labels = mixedMoment B raw14137step0 raw14137step0Labels := by
      have hz : ∀ j, raw14137 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14137step0 = (fun i j => raw14137 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14137step0 raw14137; decide +kernel
      have hl : raw14137step0Labels = raw14137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14137 raw14137Labels permutation265 hz
    mixedMoment B raw14137step0 raw14137step0Labels = mixedMoment B raw14137step1 raw14137step1Labels := by
      have ha : raw14137step1 = (fun i j => raw14137step0 (permutation95 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14137step1 raw14137step0; decide +kernel
      have hl : raw14137step1Labels = raw14137step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14137step0 raw14137step0Labels permutation95 permutation5
    mixedMoment B raw14137step1 raw14137step1Labels = mixedMoment B raw14137step2 raw14137step2Labels := by
      have ha : raw14137step2 = raw14137step1 := by apply Matrix.ext; unfold raw14137step2 raw14137step1; decide +kernel
      have hl : raw14137step1Labels = labelEmbedding8 ∘ raw14137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14137step1 raw14137step1Labels raw14137step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw14138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14138step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14138 raw14138Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw14138 raw14138Labels = mixedMoment B raw14138step0 raw14138step0Labels := by
      have ha : raw14138step0 = (fun i j => raw14138 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14138step0 raw14138; decide +kernel
      have hl : raw14138step0Labels = raw14138Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14138 raw14138Labels permutation195 permutation3
    mixedMoment B raw14138step0 raw14138step0Labels = mixedMoment B raw14138step1 raw14138step1Labels := by
      have ha : raw14138step1 = raw14138step0 := by apply Matrix.ext; unfold raw14138step1 raw14138step0; decide +kernel
      have hl : raw14138step0Labels = labelEmbedding6 ∘ raw14138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14138step0 raw14138step0Labels raw14138step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw14139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14139step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14139 raw14139Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw14139 raw14139Labels = mixedMoment B raw14139step0 raw14139step0Labels := by
      have ha : raw14139step0 = (fun i j => raw14139 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14139step0 raw14139; decide +kernel
      have hl : raw14139step0Labels = raw14139Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14139 raw14139Labels permutation195 permutation3
    mixedMoment B raw14139step0 raw14139step0Labels = mixedMoment B raw14139step1 raw14139step1Labels := by
      have ha : raw14139step1 = raw14139step0 := by apply Matrix.ext; unfold raw14139step1 raw14139step0; decide +kernel
      have hl : raw14139step0Labels = labelEmbedding6 ∘ raw14139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14139step0 raw14139step0Labels raw14139step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw14140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14140step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14140 raw14140Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw14140 raw14140Labels = mixedMoment B raw14140step0 raw14140step0Labels := by
      have ha : raw14140step0 = (fun i j => raw14140 (permutation186 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14140step0 raw14140; decide +kernel
      have hl : raw14140step0Labels = raw14140Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14140 raw14140Labels permutation186 permutation3
    mixedMoment B raw14140step0 raw14140step0Labels = mixedMoment B raw14140step1 raw14140step1Labels := by
      have ha : raw14140step1 = raw14140step0 := by apply Matrix.ext; unfold raw14140step1 raw14140step0; decide +kernel
      have hl : raw14140step0Labels = labelEmbedding6 ∘ raw14140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14140step0 raw14140step0Labels raw14140step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw14141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14141 raw14141Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw14141 raw14141Labels = mixedMoment B raw14141step0 raw14141step0Labels := by
      have hz : ∀ j, raw14141 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14141step0 = (fun i j => raw14141 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14141step0 raw14141; decide +kernel
      have hl : raw14141step0Labels = raw14141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14141 raw14141Labels permutation520 hz
    mixedMoment B raw14141step0 raw14141step0Labels = mixedMoment B raw14141step1 raw14141step1Labels := by
      have ha : raw14141step1 = (fun i j => raw14141step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14141step1 raw14141step0; decide +kernel
      have hl : raw14141step1Labels = raw14141step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14141step0 raw14141step0Labels permutation42 permutation3
    mixedMoment B raw14141step1 raw14141step1Labels = mixedMoment B raw14141step2 raw14141step2Labels := by
      have ha : raw14141step2 = raw14141step1 := by apply Matrix.ext; unfold raw14141step2 raw14141step1; decide +kernel
      have hl : raw14141step1Labels = labelEmbedding6 ∘ raw14141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14141step1 raw14141step1Labels raw14141step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw14142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14142step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14142 raw14142Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw14142 raw14142Labels = mixedMoment B raw14142step0 raw14142step0Labels := by
      have ha : raw14142step0 = (fun i j => raw14142 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14142step0 raw14142; decide +kernel
      have hl : raw14142step0Labels = raw14142Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14142 raw14142Labels permutation195 permutation3
    mixedMoment B raw14142step0 raw14142step0Labels = mixedMoment B raw14142step1 raw14142step1Labels := by
      have ha : raw14142step1 = raw14142step0 := by apply Matrix.ext; unfold raw14142step1 raw14142step0; decide +kernel
      have hl : raw14142step0Labels = labelEmbedding6 ∘ raw14142step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14142step0 raw14142step0Labels raw14142step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw14143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14143 raw14143Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw14143 raw14143Labels = mixedMoment B raw14143step0 raw14143step0Labels := by
      have hz : ∀ j, raw14143 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14143step0 = (fun i j => raw14143 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14143step0 raw14143; decide +kernel
      have hl : raw14143step0Labels = raw14143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14143 raw14143Labels permutation265 hz
    mixedMoment B raw14143step0 raw14143step0Labels = mixedMoment B raw14143step1 raw14143step1Labels := by
      have ha : raw14143step1 = (fun i j => raw14143step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14143step1 raw14143step0; decide +kernel
      have hl : raw14143step1Labels = raw14143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14143step0 raw14143step0Labels permutation37 permutation3
    mixedMoment B raw14143step1 raw14143step1Labels = mixedMoment B raw14143step2 raw14143step2Labels := by
      have ha : raw14143step2 = raw14143step1 := by apply Matrix.ext; unfold raw14143step2 raw14143step1; decide +kernel
      have hl : raw14143step1Labels = labelEmbedding6 ∘ raw14143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14143step1 raw14143step1Labels raw14143step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw14144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14144step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14144 raw14144Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw14144 raw14144Labels = mixedMoment B raw14144step0 raw14144step0Labels := by
      have ha : raw14144step0 = (fun i j => raw14144 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14144step0 raw14144; decide +kernel
      have hl : raw14144step0Labels = raw14144Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14144 raw14144Labels permutation157 permutation3
    mixedMoment B raw14144step0 raw14144step0Labels = mixedMoment B raw14144step1 raw14144step1Labels := by
      have ha : raw14144step1 = raw14144step0 := by apply Matrix.ext; unfold raw14144step1 raw14144step0; decide +kernel
      have hl : raw14144step0Labels = labelEmbedding6 ∘ raw14144step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14144step0 raw14144step0Labels raw14144step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw14145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14145 raw14145Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14145 raw14145Labels = mixedMoment B raw14145step0 raw14145step0Labels := by
      have hz : ∀ j, raw14145 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14145step0 = (fun i j => raw14145 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14145step0 raw14145; decide +kernel
      have hl : raw14145step0Labels = raw14145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14145 raw14145Labels permutation265 hz
    mixedMoment B raw14145step0 raw14145step0Labels = mixedMoment B raw14145step1 raw14145step1Labels := by
      have ha : raw14145step1 = (fun i j => raw14145step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14145step1 raw14145step0; decide +kernel
      have hl : raw14145step1Labels = raw14145step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14145step0 raw14145step0Labels permutation39 permutation3
    mixedMoment B raw14145step1 raw14145step1Labels = mixedMoment B raw14145step2 raw14145step2Labels := by
      have ha : raw14145step2 = raw14145step1 := by apply Matrix.ext; unfold raw14145step2 raw14145step1; decide +kernel
      have hl : raw14145step1Labels = labelEmbedding6 ∘ raw14145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14145step1 raw14145step1Labels raw14145step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw14146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14146step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14146step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14146step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14146 raw14146Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw14146 raw14146Labels = mixedMoment B raw14146step0 raw14146step0Labels := by
      have hz : ∀ j, raw14146 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14146step0 = (fun i j => raw14146 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14146step0 raw14146; decide +kernel
      have hl : raw14146step0Labels = raw14146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14146 raw14146Labels permutation520 hz
    mixedMoment B raw14146step0 raw14146step0Labels = mixedMoment B raw14146step1 raw14146step1Labels := by
      have hz : ∀ j, raw14146step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14146step1 = (fun i j => raw14146step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14146step1 raw14146step0; decide +kernel
      have hl : raw14146step1Labels = raw14146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14146step0 raw14146step0Labels permutation56 hz
    mixedMoment B raw14146step1 raw14146step1Labels = mixedMoment B raw14146step2 raw14146step2Labels := by
      have ha : raw14146step2 = (fun i j => raw14146step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14146step2 raw14146step1; decide +kernel
      have hl : raw14146step2Labels = raw14146step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14146step1 raw14146step1Labels permutation9 permutation3
    mixedMoment B raw14146step2 raw14146step2Labels = mixedMoment B raw14146step3 raw14146step3Labels := by
      have ha : raw14146step3 = raw14146step2 := by apply Matrix.ext; unfold raw14146step3 raw14146step2; decide +kernel
      have hl : raw14146step2Labels = labelEmbedding6 ∘ raw14146step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14146step2 raw14146step2Labels raw14146step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw14147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14147 raw14147Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw14147 raw14147Labels = mixedMoment B raw14147step0 raw14147step0Labels := by
      have hz : ∀ j, raw14147 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14147step0 = (fun i j => raw14147 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14147step0 raw14147; decide +kernel
      have hl : raw14147step0Labels = raw14147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14147 raw14147Labels permutation265 hz
    mixedMoment B raw14147step0 raw14147step0Labels = mixedMoment B raw14147step1 raw14147step1Labels := by
      have ha : raw14147step1 = (fun i j => raw14147step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14147step1 raw14147step0; decide +kernel
      have hl : raw14147step1Labels = raw14147step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14147step0 raw14147step0Labels permutation51 permutation3
    mixedMoment B raw14147step1 raw14147step1Labels = mixedMoment B raw14147step2 raw14147step2Labels := by
      have ha : raw14147step2 = raw14147step1 := by apply Matrix.ext; unfold raw14147step2 raw14147step1; decide +kernel
      have hl : raw14147step1Labels = labelEmbedding6 ∘ raw14147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14147step1 raw14147step1Labels raw14147step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw14148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14148 raw14148Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw14148 raw14148Labels = mixedMoment B raw14148step0 raw14148step0Labels := by
      have hz : ∀ j, raw14148 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14148step0 = (fun i j => raw14148 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14148step0 raw14148; decide +kernel
      have hl : raw14148step0Labels = raw14148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14148 raw14148Labels permutation265 hz
    mixedMoment B raw14148step0 raw14148step0Labels = mixedMoment B raw14148step1 raw14148step1Labels := by
      have ha : raw14148step1 = (fun i j => raw14148step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14148step1 raw14148step0; decide +kernel
      have hl : raw14148step1Labels = raw14148step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14148step0 raw14148step0Labels permutation37 permutation3
    mixedMoment B raw14148step1 raw14148step1Labels = mixedMoment B raw14148step2 raw14148step2Labels := by
      have ha : raw14148step2 = raw14148step1 := by apply Matrix.ext; unfold raw14148step2 raw14148step1; decide +kernel
      have hl : raw14148step1Labels = labelEmbedding6 ∘ raw14148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14148step1 raw14148step1Labels raw14148step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw14149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14149step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14149 raw14149Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw14149 raw14149Labels = mixedMoment B raw14149step0 raw14149step0Labels := by
      have ha : raw14149step0 = (fun i j => raw14149 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14149step0 raw14149; decide +kernel
      have hl : raw14149step0Labels = raw14149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14149 raw14149Labels permutation157 permutation3
    mixedMoment B raw14149step0 raw14149step0Labels = mixedMoment B raw14149step1 raw14149step1Labels := by
      have ha : raw14149step1 = raw14149step0 := by apply Matrix.ext; unfold raw14149step1 raw14149step0; decide +kernel
      have hl : raw14149step0Labels = labelEmbedding6 ∘ raw14149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14149step0 raw14149step0Labels raw14149step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5055 node5055Labels := by rfl

def raw14150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14150 raw14150Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw14150 raw14150Labels = mixedMoment B raw14150step0 raw14150step0Labels := by
      have hz : ∀ j, raw14150 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14150step0 = (fun i j => raw14150 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14150step0 raw14150; decide +kernel
      have hl : raw14150step0Labels = raw14150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14150 raw14150Labels permutation265 hz
    mixedMoment B raw14150step0 raw14150step0Labels = mixedMoment B raw14150step1 raw14150step1Labels := by
      have ha : raw14150step1 = (fun i j => raw14150step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14150step1 raw14150step0; decide +kernel
      have hl : raw14150step1Labels = raw14150step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14150step0 raw14150step0Labels permutation37 permutation3
    mixedMoment B raw14150step1 raw14150step1Labels = mixedMoment B raw14150step2 raw14150step2Labels := by
      have ha : raw14150step2 = raw14150step1 := by apply Matrix.ext; unfold raw14150step2 raw14150step1; decide +kernel
      have hl : raw14150step1Labels = labelEmbedding6 ∘ raw14150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14150step1 raw14150step1Labels raw14150step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw14151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw14151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw14151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14151step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw14151step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14151step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw14151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14151 raw14151Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw14151 raw14151Labels = mixedMoment B raw14151step0 raw14151step0Labels := by
      have hz : ∀ j, raw14151 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14151step0 = (fun i j => raw14151 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14151step0 raw14151; decide +kernel
      have hl : raw14151step0Labels = raw14151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14151 raw14151Labels permutation520 hz
    mixedMoment B raw14151step0 raw14151step0Labels = mixedMoment B raw14151step1 raw14151step1Labels := by
      have hz : ∀ j, raw14151step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14151step1 = (fun i j => raw14151step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14151step1 raw14151step0; decide +kernel
      have hl : raw14151step1Labels = raw14151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14151step0 raw14151step0Labels permutation56 hz
    mixedMoment B raw14151step1 raw14151step1Labels = mixedMoment B raw14151step2 raw14151step2Labels := by
      have ha : raw14151step2 = (fun i j => raw14151step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14151step2 raw14151step1; decide +kernel
      have hl : raw14151step2Labels = raw14151step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14151step1 raw14151step1Labels permutation9 permutation3
    mixedMoment B raw14151step2 raw14151step2Labels = mixedMoment B raw14151step3 raw14151step3Labels := by
      have ha : raw14151step3 = raw14151step2 := by apply Matrix.ext; unfold raw14151step3 raw14151step2; decide +kernel
      have hl : raw14151step2Labels = labelEmbedding6 ∘ raw14151step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14151step2 raw14151step2Labels raw14151step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw14152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw14152step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw14152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14152 raw14152Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw14152 raw14152Labels = mixedMoment B raw14152step0 raw14152step0Labels := by
      have hz : ∀ j, raw14152 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14152step0 = (fun i j => raw14152 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14152step0 raw14152; decide +kernel
      have hl : raw14152step0Labels = raw14152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14152 raw14152Labels permutation265 hz
    mixedMoment B raw14152step0 raw14152step0Labels = mixedMoment B raw14152step1 raw14152step1Labels := by
      have ha : raw14152step1 = (fun i j => raw14152step0 (permutation95 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14152step1 raw14152step0; decide +kernel
      have hl : raw14152step1Labels = raw14152step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14152step0 raw14152step0Labels permutation95 permutation5
    mixedMoment B raw14152step1 raw14152step1Labels = mixedMoment B raw14152step2 raw14152step2Labels := by
      have ha : raw14152step2 = raw14152step1 := by apply Matrix.ext; unfold raw14152step2 raw14152step1; decide +kernel
      have hl : raw14152step1Labels = labelEmbedding8 ∘ raw14152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14152step1 raw14152step1Labels raw14152step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw14153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14153step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14153 raw14153Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw14153 raw14153Labels = mixedMoment B raw14153step0 raw14153step0Labels := by
      have hz : ∀ j, raw14153 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14153step0 = (fun i j => raw14153 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14153step0 raw14153; decide +kernel
      have hl : raw14153step0Labels = raw14153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14153 raw14153Labels permutation265 hz
    mixedMoment B raw14153step0 raw14153step0Labels = mixedMoment B raw14153step1 raw14153step1Labels := by
      have ha : raw14153step1 = (fun i j => raw14153step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14153step1 raw14153step0; decide +kernel
      have hl : raw14153step1Labels = raw14153step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14153step0 raw14153step0Labels permutation36 permutation3
    mixedMoment B raw14153step1 raw14153step1Labels = mixedMoment B raw14153step2 raw14153step2Labels := by
      have ha : raw14153step2 = raw14153step1 := by apply Matrix.ext; unfold raw14153step2 raw14153step1; decide +kernel
      have hl : raw14153step1Labels = labelEmbedding6 ∘ raw14153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14153step1 raw14153step1Labels raw14153step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw14154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14154step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14154 raw14154Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw14154 raw14154Labels = mixedMoment B raw14154step0 raw14154step0Labels := by
      have ha : raw14154step0 = (fun i j => raw14154 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14154step0 raw14154; decide +kernel
      have hl : raw14154step0Labels = raw14154Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14154 raw14154Labels permutation156 permutation3
    mixedMoment B raw14154step0 raw14154step0Labels = mixedMoment B raw14154step1 raw14154step1Labels := by
      have ha : raw14154step1 = raw14154step0 := by apply Matrix.ext; unfold raw14154step1 raw14154step0; decide +kernel
      have hl : raw14154step0Labels = labelEmbedding6 ∘ raw14154step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14154step0 raw14154step0Labels raw14154step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw14155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14155step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14155 raw14155Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw14155 raw14155Labels = mixedMoment B raw14155step0 raw14155step0Labels := by
      have hz : ∀ j, raw14155 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14155step0 = (fun i j => raw14155 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14155step0 raw14155; decide +kernel
      have hl : raw14155step0Labels = raw14155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14155 raw14155Labels permutation265 hz
    mixedMoment B raw14155step0 raw14155step0Labels = mixedMoment B raw14155step1 raw14155step1Labels := by
      have ha : raw14155step1 = (fun i j => raw14155step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14155step1 raw14155step0; decide +kernel
      have hl : raw14155step1Labels = raw14155step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14155step0 raw14155step0Labels permutation36 permutation3
    mixedMoment B raw14155step1 raw14155step1Labels = mixedMoment B raw14155step2 raw14155step2Labels := by
      have ha : raw14155step2 = raw14155step1 := by apply Matrix.ext; unfold raw14155step2 raw14155step1; decide +kernel
      have hl : raw14155step1Labels = labelEmbedding6 ∘ raw14155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14155step1 raw14155step1Labels raw14155step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw14156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14156step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14156step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14156 raw14156Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw14156 raw14156Labels = mixedMoment B raw14156step0 raw14156step0Labels := by
      have hz : ∀ j, raw14156 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14156step0 = (fun i j => raw14156 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14156step0 raw14156; decide +kernel
      have hl : raw14156step0Labels = raw14156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14156 raw14156Labels permutation265 hz
    mixedMoment B raw14156step0 raw14156step0Labels = mixedMoment B raw14156step1 raw14156step1Labels := by
      have ha : raw14156step1 = (fun i j => raw14156step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14156step1 raw14156step0; decide +kernel
      have hl : raw14156step1Labels = raw14156step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14156step0 raw14156step0Labels permutation33 permutation3
    mixedMoment B raw14156step1 raw14156step1Labels = mixedMoment B raw14156step2 raw14156step2Labels := by
      have ha : raw14156step2 = raw14156step1 := by apply Matrix.ext; unfold raw14156step2 raw14156step1; decide +kernel
      have hl : raw14156step1Labels = labelEmbedding6 ∘ raw14156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14156step1 raw14156step1Labels raw14156step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw14157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw14157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw14157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14157step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14157 raw14157Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw14157 raw14157Labels = mixedMoment B raw14157step0 raw14157step0Labels := by
      have hz : ∀ j, raw14157 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14157step0 = (fun i j => raw14157 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14157step0 raw14157; decide +kernel
      have hl : raw14157step0Labels = raw14157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14157 raw14157Labels permutation265 hz
    mixedMoment B raw14157step0 raw14157step0Labels = mixedMoment B raw14157step1 raw14157step1Labels := by
      have ha : raw14157step1 = (fun i j => raw14157step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14157step1 raw14157step0; decide +kernel
      have hl : raw14157step1Labels = raw14157step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14157step0 raw14157step0Labels permutation36 permutation3
    mixedMoment B raw14157step1 raw14157step1Labels = mixedMoment B raw14157step2 raw14157step2Labels := by
      have ha : raw14157step2 = raw14157step1 := by apply Matrix.ext; unfold raw14157step2 raw14157step1; decide +kernel
      have hl : raw14157step1Labels = labelEmbedding6 ∘ raw14157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14157step1 raw14157step1Labels raw14157step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw14158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14158step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14158step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14158 raw14158Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw14158 raw14158Labels = mixedMoment B raw14158step0 raw14158step0Labels := by
      have hz : ∀ j, raw14158 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14158step0 = (fun i j => raw14158 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14158step0 raw14158; decide +kernel
      have hl : raw14158step0Labels = raw14158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14158 raw14158Labels permutation265 hz
    mixedMoment B raw14158step0 raw14158step0Labels = mixedMoment B raw14158step1 raw14158step1Labels := by
      have ha : raw14158step1 = (fun i j => raw14158step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14158step1 raw14158step0; decide +kernel
      have hl : raw14158step1Labels = raw14158step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14158step0 raw14158step0Labels permutation34 permutation3
    mixedMoment B raw14158step1 raw14158step1Labels = mixedMoment B raw14158step2 raw14158step2Labels := by
      have ha : raw14158step2 = raw14158step1 := by apply Matrix.ext; unfold raw14158step2 raw14158step1; decide +kernel
      have hl : raw14158step1Labels = labelEmbedding6 ∘ raw14158step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14158step1 raw14158step1Labels raw14158step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw14159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14159step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14159 raw14159Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw14159 raw14159Labels = mixedMoment B raw14159step0 raw14159step0Labels := by
      have ha : raw14159step0 = (fun i j => raw14159 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14159step0 raw14159; decide +kernel
      have hl : raw14159step0Labels = raw14159Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14159 raw14159Labels permutation154 permutation3
    mixedMoment B raw14159step0 raw14159step0Labels = mixedMoment B raw14159step1 raw14159step1Labels := by
      have ha : raw14159step1 = raw14159step0 := by apply Matrix.ext; unfold raw14159step1 raw14159step0; decide +kernel
      have hl : raw14159step0Labels = labelEmbedding6 ∘ raw14159step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14159step0 raw14159step0Labels raw14159step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw14160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14160step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14160step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14160 raw14160Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw14160 raw14160Labels = mixedMoment B raw14160step0 raw14160step0Labels := by
      have hz : ∀ j, raw14160 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14160step0 = (fun i j => raw14160 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14160step0 raw14160; decide +kernel
      have hl : raw14160step0Labels = raw14160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14160 raw14160Labels permutation265 hz
    mixedMoment B raw14160step0 raw14160step0Labels = mixedMoment B raw14160step1 raw14160step1Labels := by
      have ha : raw14160step1 = (fun i j => raw14160step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14160step1 raw14160step0; decide +kernel
      have hl : raw14160step1Labels = raw14160step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14160step0 raw14160step0Labels permutation34 permutation3
    mixedMoment B raw14160step1 raw14160step1Labels = mixedMoment B raw14160step2 raw14160step2Labels := by
      have ha : raw14160step2 = raw14160step1 := by apply Matrix.ext; unfold raw14160step2 raw14160step1; decide +kernel
      have hl : raw14160step1Labels = labelEmbedding6 ∘ raw14160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14160step1 raw14160step1Labels raw14160step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw14161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14161step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14161step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14161 raw14161Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14161 raw14161Labels = mixedMoment B raw14161step0 raw14161step0Labels := by
      have hz : ∀ j, raw14161 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14161step0 = (fun i j => raw14161 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14161step0 raw14161; decide +kernel
      have hl : raw14161step0Labels = raw14161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14161 raw14161Labels permutation265 hz
    mixedMoment B raw14161step0 raw14161step0Labels = mixedMoment B raw14161step1 raw14161step1Labels := by
      have ha : raw14161step1 = (fun i j => raw14161step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14161step1 raw14161step0; decide +kernel
      have hl : raw14161step1Labels = raw14161step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14161step0 raw14161step0Labels permutation32 permutation3
    mixedMoment B raw14161step1 raw14161step1Labels = mixedMoment B raw14161step2 raw14161step2Labels := by
      have ha : raw14161step2 = raw14161step1 := by apply Matrix.ext; unfold raw14161step2 raw14161step1; decide +kernel
      have hl : raw14161step1Labels = labelEmbedding6 ∘ raw14161step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14161step1 raw14161step1Labels raw14161step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw14162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw14162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw14162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw14162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14162step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14162step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14162step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14162step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14162 raw14162Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw14162 raw14162Labels = mixedMoment B raw14162step0 raw14162step0Labels := by
      have hz : ∀ j, raw14162 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14162step0 = (fun i j => raw14162 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14162step0 raw14162; decide +kernel
      have hl : raw14162step0Labels = raw14162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14162 raw14162Labels permutation520 hz
    mixedMoment B raw14162step0 raw14162step0Labels = mixedMoment B raw14162step1 raw14162step1Labels := by
      have hz : ∀ j, raw14162step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14162step1 = (fun i j => raw14162step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14162step1 raw14162step0; decide +kernel
      have hl : raw14162step1Labels = raw14162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14162step0 raw14162step0Labels permutation56 hz
    mixedMoment B raw14162step1 raw14162step1Labels = mixedMoment B raw14162step2 raw14162step2Labels := by
      have ha : raw14162step2 = (fun i j => raw14162step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14162step2 raw14162step1; decide +kernel
      have hl : raw14162step2Labels = raw14162step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14162step1 raw14162step1Labels permutation8 permutation3
    mixedMoment B raw14162step2 raw14162step2Labels = mixedMoment B raw14162step3 raw14162step3Labels := by
      have ha : raw14162step3 = raw14162step2 := by apply Matrix.ext; unfold raw14162step3 raw14162step2; decide +kernel
      have hl : raw14162step2Labels = labelEmbedding6 ∘ raw14162step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14162step2 raw14162step2Labels raw14162step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw14163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14163 raw14163Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw14163 raw14163Labels = mixedMoment B raw14163step0 raw14163step0Labels := by
      have ha : raw14163step0 = (fun i j => raw14163 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14163step0 raw14163; decide +kernel
      have hl : raw14163step0Labels = raw14163Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14163 raw14163Labels permutation157 permutation3
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw14164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14164 raw14164Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw14164 raw14164Labels = mixedMoment B raw14164step0 raw14164step0Labels := by
      have hz : ∀ j, raw14164 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14164step0 = (fun i j => raw14164 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14164step0 raw14164; decide +kernel
      have hl : raw14164step0Labels = raw14164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14164 raw14164Labels permutation265 hz
    mixedMoment B raw14164step0 raw14164step0Labels = mixedMoment B raw14164step1 raw14164step1Labels := by
      have ha : raw14164step1 = (fun i j => raw14164step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14164step1 raw14164step0; decide +kernel
      have hl : raw14164step1Labels = raw14164step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14164step0 raw14164step0Labels permutation37 permutation3
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw14165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw14165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14165 raw14165Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw14165 raw14165Labels = mixedMoment B raw14165step0 raw14165step0Labels := by
      have hz : ∀ j, raw14165 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14165step0 = (fun i j => raw14165 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14165step0 raw14165; decide +kernel
      have hl : raw14165step0Labels = raw14165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14165 raw14165Labels permutation265 hz
    mixedMoment B raw14165step0 raw14165step0Labels = mixedMoment B raw14165step1 raw14165step1Labels := by
      have ha : raw14165step1 = (fun i j => raw14165step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14165step1 raw14165step0; decide +kernel
      have hl : raw14165step1Labels = raw14165step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14165step0 raw14165step0Labels permutation33 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw14166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14166 raw14166Labels = mixedMoment B node4015 node4015Labels := by
  calc
    mixedMoment B raw14166 raw14166Labels = mixedMoment B raw14166step0 raw14166step0Labels := by
      have hz : ∀ j, raw14166 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14166step0 = (fun i j => raw14166 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14166step0 raw14166; decide +kernel
      have hl : raw14166step0Labels = raw14166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14166 raw14166Labels permutation520 hz
    mixedMoment B raw14166step0 raw14166step0Labels = mixedMoment B raw14166step1 raw14166step1Labels := by
      have hz : ∀ j, raw14166step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14166step1 = (fun i j => raw14166step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14166step1 raw14166step0; decide +kernel
      have hl : raw14166step1Labels = raw14166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14166step0 raw14166step0Labels permutation56 hz
    mixedMoment B raw14166step1 raw14166step1Labels = mixedMoment B raw14166step2 raw14166step2Labels := by
      have ha : raw14166step2 = (fun i j => raw14166step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14166step2 raw14166step1; decide +kernel
      have hl : raw14166step2Labels = raw14166step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14166step1 raw14166step1Labels permutation9 permutation3
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw14167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14167 raw14167Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw14167 raw14167Labels = mixedMoment B raw14167step0 raw14167step0Labels := by
      have hz : ∀ j, raw14167 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14167step0 = (fun i j => raw14167 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14167step0 raw14167; decide +kernel
      have hl : raw14167step0Labels = raw14167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14167 raw14167Labels permutation265 hz
    mixedMoment B raw14167step0 raw14167step0Labels = mixedMoment B raw14167step1 raw14167step1Labels := by
      have ha : raw14167step1 = (fun i j => raw14167step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14167step1 raw14167step0; decide +kernel
      have hl : raw14167step1Labels = raw14167step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14167step0 raw14167step0Labels permutation37 permutation3
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw14168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14168 raw14168Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw14168 raw14168Labels = mixedMoment B raw14168step0 raw14168step0Labels := by
      have ha : raw14168step0 = (fun i j => raw14168 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14168step0 raw14168; decide +kernel
      have hl : raw14168step0Labels = raw14168Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14168 raw14168Labels permutation195 permutation3
    _ = mixedMoment B node998 node998Labels := by rfl

def raw14169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14169 raw14169Labels = mixedMoment B node2398 node2398Labels := by
  calc
    mixedMoment B raw14169 raw14169Labels = mixedMoment B raw14169step0 raw14169step0Labels := by
      have ha : raw14169step0 = (fun i j => raw14169 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14169step0 raw14169; decide +kernel
      have hl : raw14169step0Labels = raw14169Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14169 raw14169Labels permutation195 permutation3
    _ = mixedMoment B node2398 node2398Labels := by rfl

def raw14170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14170 raw14170Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw14170 raw14170Labels = mixedMoment B raw14170step0 raw14170step0Labels := by
      have ha : raw14170step0 = (fun i j => raw14170 (permutation186 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14170step0 raw14170; decide +kernel
      have hl : raw14170step0Labels = raw14170Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14170 raw14170Labels permutation186 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw14171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14171 raw14171Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw14171 raw14171Labels = mixedMoment B raw14171step0 raw14171step0Labels := by
      have hz : ∀ j, raw14171 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14171step0 = (fun i j => raw14171 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14171step0 raw14171; decide +kernel
      have hl : raw14171step0Labels = raw14171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14171 raw14171Labels permutation520 hz
    mixedMoment B raw14171step0 raw14171step0Labels = mixedMoment B raw14171step1 raw14171step1Labels := by
      have ha : raw14171step1 = (fun i j => raw14171step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14171step1 raw14171step0; decide +kernel
      have hl : raw14171step1Labels = raw14171step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14171step0 raw14171step0Labels permutation42 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw14172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14172 raw14172Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw14172 raw14172Labels = mixedMoment B raw14172step0 raw14172step0Labels := by
      have ha : raw14172step0 = (fun i j => raw14172 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14172step0 raw14172; decide +kernel
      have hl : raw14172step0Labels = raw14172Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14172 raw14172Labels permutation195 permutation3
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw14173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14173 raw14173Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw14173 raw14173Labels = mixedMoment B raw14173step0 raw14173step0Labels := by
      have hz : ∀ j, raw14173 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14173step0 = (fun i j => raw14173 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14173step0 raw14173; decide +kernel
      have hl : raw14173step0Labels = raw14173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14173 raw14173Labels permutation265 hz
    mixedMoment B raw14173step0 raw14173step0Labels = mixedMoment B raw14173step1 raw14173step1Labels := by
      have ha : raw14173step1 = (fun i j => raw14173step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14173step1 raw14173step0; decide +kernel
      have hl : raw14173step1Labels = raw14173step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14173step0 raw14173step0Labels permutation37 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw14174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14174 raw14174Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw14174 raw14174Labels = mixedMoment B raw14174step0 raw14174step0Labels := by
      have ha : raw14174step0 = (fun i j => raw14174 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14174step0 raw14174; decide +kernel
      have hl : raw14174step0Labels = raw14174Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14174 raw14174Labels permutation157 permutation3
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw14175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14175 raw14175Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw14175 raw14175Labels = mixedMoment B raw14175step0 raw14175step0Labels := by
      have hz : ∀ j, raw14175 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14175step0 = (fun i j => raw14175 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14175step0 raw14175; decide +kernel
      have hl : raw14175step0Labels = raw14175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14175 raw14175Labels permutation265 hz
    mixedMoment B raw14175step0 raw14175step0Labels = mixedMoment B raw14175step1 raw14175step1Labels := by
      have ha : raw14175step1 = (fun i j => raw14175step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14175step1 raw14175step0; decide +kernel
      have hl : raw14175step1Labels = raw14175step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14175step0 raw14175step0Labels permutation39 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw14176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw14176step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14176 raw14176Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw14176 raw14176Labels = mixedMoment B raw14176step0 raw14176step0Labels := by
      have hz : ∀ j, raw14176 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14176step0 = (fun i j => raw14176 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14176step0 raw14176; decide +kernel
      have hl : raw14176step0Labels = raw14176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14176 raw14176Labels permutation520 hz
    mixedMoment B raw14176step0 raw14176step0Labels = mixedMoment B raw14176step1 raw14176step1Labels := by
      have hz : ∀ j, raw14176step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14176step1 = (fun i j => raw14176step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14176step1 raw14176step0; decide +kernel
      have hl : raw14176step1Labels = raw14176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14176step0 raw14176step0Labels permutation56 hz
    mixedMoment B raw14176step1 raw14176step1Labels = mixedMoment B raw14176step2 raw14176step2Labels := by
      have ha : raw14176step2 = (fun i j => raw14176step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14176step2 raw14176step1; decide +kernel
      have hl : raw14176step2Labels = raw14176step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14176step1 raw14176step1Labels permutation9 permutation3
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw14177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14177 raw14177Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw14177 raw14177Labels = mixedMoment B raw14177step0 raw14177step0Labels := by
      have hz : ∀ j, raw14177 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14177step0 = (fun i j => raw14177 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14177step0 raw14177; decide +kernel
      have hl : raw14177step0Labels = raw14177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14177 raw14177Labels permutation265 hz
    mixedMoment B raw14177step0 raw14177step0Labels = mixedMoment B raw14177step1 raw14177step1Labels := by
      have ha : raw14177step1 = (fun i j => raw14177step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14177step1 raw14177step0; decide +kernel
      have hl : raw14177step1Labels = raw14177step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14177step0 raw14177step0Labels permutation51 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw14178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14178 raw14178Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw14178 raw14178Labels = mixedMoment B raw14178step0 raw14178step0Labels := by
      have hz : ∀ j, raw14178 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14178step0 = (fun i j => raw14178 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14178step0 raw14178; decide +kernel
      have hl : raw14178step0Labels = raw14178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14178 raw14178Labels permutation265 hz
    mixedMoment B raw14178step0 raw14178step0Labels = mixedMoment B raw14178step1 raw14178step1Labels := by
      have ha : raw14178step1 = (fun i j => raw14178step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14178step1 raw14178step0; decide +kernel
      have hl : raw14178step1Labels = raw14178step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14178step0 raw14178step0Labels permutation37 permutation3
    _ = mixedMoment B node999 node999Labels := by rfl

def raw14179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14179 raw14179Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw14179 raw14179Labels = mixedMoment B raw14179step0 raw14179step0Labels := by
      have ha : raw14179step0 = (fun i j => raw14179 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14179step0 raw14179; decide +kernel
      have hl : raw14179step0Labels = raw14179Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14179 raw14179Labels permutation157 permutation3
    _ = mixedMoment B node2458 node2458Labels := by rfl

def raw14180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw14180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14180 raw14180Labels = mixedMoment B node2399 node2399Labels := by
  calc
    mixedMoment B raw14180 raw14180Labels = mixedMoment B raw14180step0 raw14180step0Labels := by
      have hz : ∀ j, raw14180 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14180step0 = (fun i j => raw14180 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14180step0 raw14180; decide +kernel
      have hl : raw14180step0Labels = raw14180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14180 raw14180Labels permutation265 hz
    mixedMoment B raw14180step0 raw14180step0Labels = mixedMoment B raw14180step1 raw14180step1Labels := by
      have ha : raw14180step1 = (fun i j => raw14180step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14180step1 raw14180step0; decide +kernel
      have hl : raw14180step1Labels = raw14180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14180step0 raw14180step0Labels permutation37 permutation3
    _ = mixedMoment B node2399 node2399Labels := by rfl

def raw14181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw14181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw14181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw14181step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw14181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14181 raw14181Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw14181 raw14181Labels = mixedMoment B raw14181step0 raw14181step0Labels := by
      have hz : ∀ j, raw14181 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14181step0 = (fun i j => raw14181 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14181step0 raw14181; decide +kernel
      have hl : raw14181step0Labels = raw14181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14181 raw14181Labels permutation520 hz
    mixedMoment B raw14181step0 raw14181step0Labels = mixedMoment B raw14181step1 raw14181step1Labels := by
      have hz : ∀ j, raw14181step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14181step1 = (fun i j => raw14181step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14181step1 raw14181step0; decide +kernel
      have hl : raw14181step1Labels = raw14181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14181step0 raw14181step0Labels permutation56 hz
    mixedMoment B raw14181step1 raw14181step1Labels = mixedMoment B raw14181step2 raw14181step2Labels := by
      have ha : raw14181step2 = (fun i j => raw14181step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14181step2 raw14181step1; decide +kernel
      have hl : raw14181step2Labels = raw14181step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14181step1 raw14181step1Labels permutation9 permutation3
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw14182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw14182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw14182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14182 raw14182Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw14182 raw14182Labels = mixedMoment B raw14182step0 raw14182step0Labels := by
      have hz : ∀ j, raw14182 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14182step0 = (fun i j => raw14182 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14182step0 raw14182; decide +kernel
      have hl : raw14182step0Labels = raw14182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14182 raw14182Labels permutation265 hz
    mixedMoment B raw14182step0 raw14182step0Labels = mixedMoment B raw14182step1 raw14182step1Labels := by
      have ha : raw14182step1 = (fun i j => raw14182step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14182step1 raw14182step0; decide +kernel
      have hl : raw14182step1Labels = raw14182step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14182step0 raw14182step0Labels permutation37 permutation3
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw14183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14183 raw14183Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw14183 raw14183Labels = mixedMoment B raw14183step0 raw14183step0Labels := by
      have hz : ∀ j, raw14183 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14183step0 = (fun i j => raw14183 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14183step0 raw14183; decide +kernel
      have hl : raw14183step0Labels = raw14183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14183 raw14183Labels permutation265 hz
    mixedMoment B raw14183step0 raw14183step0Labels = mixedMoment B raw14183step1 raw14183step1Labels := by
      have ha : raw14183step1 = (fun i j => raw14183step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14183step1 raw14183step0; decide +kernel
      have hl : raw14183step1Labels = raw14183step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14183step0 raw14183step0Labels permutation36 permutation3
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw14184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14184 raw14184Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw14184 raw14184Labels = mixedMoment B raw14184step0 raw14184step0Labels := by
      have ha : raw14184step0 = (fun i j => raw14184 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14184step0 raw14184; decide +kernel
      have hl : raw14184step0Labels = raw14184Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14184 raw14184Labels permutation156 permutation3
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw14185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14185 raw14185Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw14185 raw14185Labels = mixedMoment B raw14185step0 raw14185step0Labels := by
      have hz : ∀ j, raw14185 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14185step0 = (fun i j => raw14185 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14185step0 raw14185; decide +kernel
      have hl : raw14185step0Labels = raw14185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14185 raw14185Labels permutation265 hz
    mixedMoment B raw14185step0 raw14185step0Labels = mixedMoment B raw14185step1 raw14185step1Labels := by
      have ha : raw14185step1 = (fun i j => raw14185step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14185step1 raw14185step0; decide +kernel
      have hl : raw14185step1Labels = raw14185step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14185step0 raw14185step0Labels permutation36 permutation3
    _ = mixedMoment B node2400 node2400Labels := by rfl

def raw14186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw14186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14186 raw14186Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw14186 raw14186Labels = mixedMoment B raw14186step0 raw14186step0Labels := by
      have hz : ∀ j, raw14186 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14186step0 = (fun i j => raw14186 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14186step0 raw14186; decide +kernel
      have hl : raw14186step0Labels = raw14186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14186 raw14186Labels permutation265 hz
    mixedMoment B raw14186step0 raw14186step0Labels = mixedMoment B raw14186step1 raw14186step1Labels := by
      have ha : raw14186step1 = (fun i j => raw14186step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14186step1 raw14186step0; decide +kernel
      have hl : raw14186step1Labels = raw14186step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14186step0 raw14186step0Labels permutation33 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw14187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw14187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw14187step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw14187step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14187 raw14187Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw14187 raw14187Labels = mixedMoment B raw14187step0 raw14187step0Labels := by
      have hz : ∀ j, raw14187 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14187step0 = (fun i j => raw14187 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14187step0 raw14187; decide +kernel
      have hl : raw14187step0Labels = raw14187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14187 raw14187Labels permutation265 hz
    mixedMoment B raw14187step0 raw14187step0Labels = mixedMoment B raw14187step1 raw14187step1Labels := by
      have ha : raw14187step1 = (fun i j => raw14187step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14187step1 raw14187step0; decide +kernel
      have hl : raw14187step1Labels = raw14187step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14187step0 raw14187step0Labels permutation36 permutation3
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw14188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14188Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14188step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14188 raw14188Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw14188 raw14188Labels = mixedMoment B raw14188step0 raw14188step0Labels := by
      have hz : ∀ j, raw14188 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14188step0 = (fun i j => raw14188 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14188step0 raw14188; decide +kernel
      have hl : raw14188step0Labels = raw14188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14188 raw14188Labels permutation265 hz
    mixedMoment B raw14188step0 raw14188step0Labels = mixedMoment B raw14188step1 raw14188step1Labels := by
      have ha : raw14188step1 = (fun i j => raw14188step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14188step1 raw14188step0; decide +kernel
      have hl : raw14188step1Labels = raw14188step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14188step0 raw14188step0Labels permutation34 permutation3
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw14189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14189step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14189 raw14189Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw14189 raw14189Labels = mixedMoment B raw14189step0 raw14189step0Labels := by
      have ha : raw14189step0 = (fun i j => raw14189 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14189step0 raw14189; decide +kernel
      have hl : raw14189step0Labels = raw14189Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14189 raw14189Labels permutation154 permutation3
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw14190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14190Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14190step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14190 raw14190Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw14190 raw14190Labels = mixedMoment B raw14190step0 raw14190step0Labels := by
      have hz : ∀ j, raw14190 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14190step0 = (fun i j => raw14190 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14190step0 raw14190; decide +kernel
      have hl : raw14190step0Labels = raw14190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14190 raw14190Labels permutation265 hz
    mixedMoment B raw14190step0 raw14190step0Labels = mixedMoment B raw14190step1 raw14190step1Labels := by
      have ha : raw14190step1 = (fun i j => raw14190step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14190step1 raw14190step0; decide +kernel
      have hl : raw14190step1Labels = raw14190step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14190step0 raw14190step0Labels permutation34 permutation3
    _ = mixedMoment B node2404 node2404Labels := by rfl

def raw14191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14191step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14191 raw14191Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw14191 raw14191Labels = mixedMoment B raw14191step0 raw14191step0Labels := by
      have hz : ∀ j, raw14191 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14191step0 = (fun i j => raw14191 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14191step0 raw14191; decide +kernel
      have hl : raw14191step0Labels = raw14191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14191 raw14191Labels permutation265 hz
    mixedMoment B raw14191step0 raw14191step0Labels = mixedMoment B raw14191step1 raw14191step1Labels := by
      have ha : raw14191step1 = (fun i j => raw14191step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14191step1 raw14191step0; decide +kernel
      have hl : raw14191step1Labels = raw14191step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14191step0 raw14191step0Labels permutation32 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw14192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw14192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw14192step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14192step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw14192step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14192step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14192 raw14192Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw14192 raw14192Labels = mixedMoment B raw14192step0 raw14192step0Labels := by
      have hz : ∀ j, raw14192 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14192step0 = (fun i j => raw14192 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14192step0 raw14192; decide +kernel
      have hl : raw14192step0Labels = raw14192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14192 raw14192Labels permutation520 hz
    mixedMoment B raw14192step0 raw14192step0Labels = mixedMoment B raw14192step1 raw14192step1Labels := by
      have hz : ∀ j, raw14192step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14192step1 = (fun i j => raw14192step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14192step1 raw14192step0; decide +kernel
      have hl : raw14192step1Labels = raw14192step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14192step0 raw14192step0Labels permutation56 hz
    mixedMoment B raw14192step1 raw14192step1Labels = mixedMoment B raw14192step2 raw14192step2Labels := by
      have ha : raw14192step2 = (fun i j => raw14192step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14192step2 raw14192step1; decide +kernel
      have hl : raw14192step2Labels = raw14192step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14192step1 raw14192step1Labels permutation8 permutation3
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw14193 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14193step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14193 raw14193Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw14193 raw14193Labels = mixedMoment B raw14193step0 raw14193step0Labels := by
      have ha : raw14193step0 = (fun i j => raw14193 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14193step0 raw14193; decide +kernel
      have hl : raw14193step0Labels = raw14193Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14193 raw14193Labels permutation152 permutation7
    mixedMoment B raw14193step0 raw14193step0Labels = mixedMoment B raw14193step1 raw14193step1Labels := by
      have ha : raw14193step1 = raw14193step0 := by apply Matrix.ext; unfold raw14193step1 raw14193step0; decide +kernel
      have hl : raw14193step0Labels = labelEmbedding10 ∘ raw14193step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14193step0 raw14193step0Labels raw14193step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw14194 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14194step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14194step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14194 raw14194Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw14194 raw14194Labels = mixedMoment B raw14194step0 raw14194step0Labels := by
      have hz : ∀ j, raw14194 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14194step0 = (fun i j => raw14194 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14194step0 raw14194; decide +kernel
      have hl : raw14194step0Labels = raw14194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14194 raw14194Labels permutation265 hz
    mixedMoment B raw14194step0 raw14194step0Labels = mixedMoment B raw14194step1 raw14194step1Labels := by
      have ha : raw14194step1 = (fun i j => raw14194step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14194step1 raw14194step0; decide +kernel
      have hl : raw14194step1Labels = raw14194step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14194step0 raw14194step0Labels permutation32 permutation7
    mixedMoment B raw14194step1 raw14194step1Labels = mixedMoment B raw14194step2 raw14194step2Labels := by
      have ha : raw14194step2 = raw14194step1 := by apply Matrix.ext; unfold raw14194step2 raw14194step1; decide +kernel
      have hl : raw14194step1Labels = labelEmbedding10 ∘ raw14194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14194step1 raw14194step1Labels raw14194step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw14195 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14195step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14195step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14195 raw14195Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw14195 raw14195Labels = mixedMoment B raw14195step0 raw14195step0Labels := by
      have hz : ∀ j, raw14195 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14195step0 = (fun i j => raw14195 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14195step0 raw14195; decide +kernel
      have hl : raw14195step0Labels = raw14195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14195 raw14195Labels permutation265 hz
    mixedMoment B raw14195step0 raw14195step0Labels = mixedMoment B raw14195step1 raw14195step1Labels := by
      have ha : raw14195step1 = (fun i j => raw14195step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14195step1 raw14195step0; decide +kernel
      have hl : raw14195step1Labels = raw14195step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14195step0 raw14195step0Labels permutation32 permutation7
    mixedMoment B raw14195step1 raw14195step1Labels = mixedMoment B raw14195step2 raw14195step2Labels := by
      have ha : raw14195step2 = raw14195step1 := by apply Matrix.ext; unfold raw14195step2 raw14195step1; decide +kernel
      have hl : raw14195step1Labels = labelEmbedding10 ∘ raw14195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14195step1 raw14195step1Labels raw14195step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw14196 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw14196step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw14196step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14196step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw14196step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14196 raw14196Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw14196 raw14196Labels = mixedMoment B raw14196step0 raw14196step0Labels := by
      have hz : ∀ j, raw14196 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14196step0 = (fun i j => raw14196 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14196step0 raw14196; decide +kernel
      have hl : raw14196step0Labels = raw14196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14196 raw14196Labels permutation265 hz
    mixedMoment B raw14196step0 raw14196step0Labels = mixedMoment B raw14196step1 raw14196step1Labels := by
      have ha : raw14196step1 = (fun i j => raw14196step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14196step1 raw14196step0; decide +kernel
      have hl : raw14196step1Labels = raw14196step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14196step0 raw14196step0Labels permutation37 permutation4
    mixedMoment B raw14196step1 raw14196step1Labels = mixedMoment B raw14196step2 raw14196step2Labels := by
      have ha : raw14196step2 = -raw14196step1 := by apply Matrix.ext; change ∀ i j, raw14196step2 i j = -(raw14196step1 i j); unfold raw14196step2 raw14196step1; decide +kernel
      have hl : raw14196step2Labels = raw14196step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14196step2 raw14196step2Labels = mixedMoment B raw14196step3 raw14196step3Labels := by
      have ha : raw14196step3 = raw14196step2 := by apply Matrix.ext; unfold raw14196step3 raw14196step2; decide +kernel
      have hl : raw14196step2Labels = labelEmbedding7 ∘ raw14196step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14196step2 raw14196step2Labels raw14196step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw14197 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw14197step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw14197step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14197 raw14197Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw14197 raw14197Labels = mixedMoment B raw14197step0 raw14197step0Labels := by
      have ha : raw14197step0 = (fun i j => raw14197 (permutation502 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14197step0 raw14197; decide +kernel
      have hl : raw14197step0Labels = raw14197Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14197 raw14197Labels permutation502 permutation5
    mixedMoment B raw14197step0 raw14197step0Labels = mixedMoment B raw14197step1 raw14197step1Labels := by
      have ha : raw14197step1 = raw14197step0 := by apply Matrix.ext; unfold raw14197step1 raw14197step0; decide +kernel
      have hl : raw14197step0Labels = labelEmbedding8 ∘ raw14197step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14197step0 raw14197step0Labels raw14197step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw14198 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw14198step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw14198step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14198 raw14198Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw14198 raw14198Labels = mixedMoment B raw14198step0 raw14198step0Labels := by
      have hz : ∀ j, raw14198 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14198step0 = (fun i j => raw14198 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14198step0 raw14198; decide +kernel
      have hl : raw14198step0Labels = raw14198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14198 raw14198Labels permutation265 hz
    mixedMoment B raw14198step0 raw14198step0Labels = mixedMoment B raw14198step1 raw14198step1Labels := by
      have ha : raw14198step1 = (fun i j => raw14198step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14198step1 raw14198step0; decide +kernel
      have hl : raw14198step1Labels = raw14198step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14198step0 raw14198step0Labels permutation96 permutation5
    mixedMoment B raw14198step1 raw14198step1Labels = mixedMoment B raw14198step2 raw14198step2Labels := by
      have ha : raw14198step2 = raw14198step1 := by apply Matrix.ext; unfold raw14198step2 raw14198step1; decide +kernel
      have hl : raw14198step1Labels = labelEmbedding8 ∘ raw14198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14198step1 raw14198step1Labels raw14198step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw14199 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw14199step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw14199step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14199 raw14199Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw14199 raw14199Labels = mixedMoment B raw14199step0 raw14199step0Labels := by
      have hz : ∀ j, raw14199 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14199step0 = (fun i j => raw14199 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14199step0 raw14199; decide +kernel
      have hl : raw14199step0Labels = raw14199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14199 raw14199Labels permutation265 hz
    mixedMoment B raw14199step0 raw14199step0Labels = mixedMoment B raw14199step1 raw14199step1Labels := by
      have ha : raw14199step1 = (fun i j => raw14199step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14199step1 raw14199step0; decide +kernel
      have hl : raw14199step1Labels = raw14199step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14199step0 raw14199step0Labels permutation35 permutation6
    mixedMoment B raw14199step1 raw14199step1Labels = mixedMoment B raw14199step2 raw14199step2Labels := by
      have ha : raw14199step2 = raw14199step1 := by apply Matrix.ext; unfold raw14199step2 raw14199step1; decide +kernel
      have hl : raw14199step1Labels = labelEmbedding9 ∘ raw14199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14199step1 raw14199step1Labels raw14199step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw14200 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw14200step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw14200step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw14200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14200 raw14200Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw14200 raw14200Labels = mixedMoment B raw14200step0 raw14200step0Labels := by
      have hz : ∀ j, raw14200 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14200step0 = (fun i j => raw14200 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14200step0 raw14200; decide +kernel
      have hl : raw14200step0Labels = raw14200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14200 raw14200Labels permutation265 hz
    mixedMoment B raw14200step0 raw14200step0Labels = mixedMoment B raw14200step1 raw14200step1Labels := by
      have ha : raw14200step1 = (fun i j => raw14200step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14200step1 raw14200step0; decide +kernel
      have hl : raw14200step1Labels = raw14200step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14200step0 raw14200step0Labels permutation36 permutation4
    mixedMoment B raw14200step1 raw14200step1Labels = mixedMoment B raw14200step2 raw14200step2Labels := by
      have ha : raw14200step2 = -raw14200step1 := by apply Matrix.ext; change ∀ i j, raw14200step2 i j = -(raw14200step1 i j); unfold raw14200step2 raw14200step1; decide +kernel
      have hl : raw14200step2Labels = raw14200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14200step2 raw14200step2Labels = mixedMoment B raw14200step3 raw14200step3Labels := by
      have ha : raw14200step3 = raw14200step2 := by apply Matrix.ext; unfold raw14200step3 raw14200step2; decide +kernel
      have hl : raw14200step2Labels = labelEmbedding7 ∘ raw14200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14200step2 raw14200step2Labels raw14200step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw14201 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14201step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14201 raw14201Labels = mixedMoment B node5246 node5246Labels := by
  calc
    mixedMoment B raw14201 raw14201Labels = mixedMoment B raw14201step0 raw14201step0Labels := by
      have ha : raw14201step0 = (fun i j => raw14201 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14201step0 raw14201; decide +kernel
      have hl : raw14201step0Labels = raw14201Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14201 raw14201Labels permutation156 permutation6
    mixedMoment B raw14201step0 raw14201step0Labels = mixedMoment B raw14201step1 raw14201step1Labels := by
      have ha : raw14201step1 = raw14201step0 := by apply Matrix.ext; unfold raw14201step1 raw14201step0; decide +kernel
      have hl : raw14201step0Labels = labelEmbedding9 ∘ raw14201step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14201step0 raw14201step0Labels raw14201step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5246 node5246Labels := by rfl

def raw14202 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14202step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14202step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14202 raw14202Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw14202 raw14202Labels = mixedMoment B raw14202step0 raw14202step0Labels := by
      have hz : ∀ j, raw14202 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14202step0 = (fun i j => raw14202 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14202step0 raw14202; decide +kernel
      have hl : raw14202step0Labels = raw14202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14202 raw14202Labels permutation265 hz
    mixedMoment B raw14202step0 raw14202step0Labels = mixedMoment B raw14202step1 raw14202step1Labels := by
      have ha : raw14202step1 = (fun i j => raw14202step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14202step1 raw14202step0; decide +kernel
      have hl : raw14202step1Labels = raw14202step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14202step0 raw14202step0Labels permutation36 permutation6
    mixedMoment B raw14202step1 raw14202step1Labels = mixedMoment B raw14202step2 raw14202step2Labels := by
      have ha : raw14202step2 = raw14202step1 := by apply Matrix.ext; unfold raw14202step2 raw14202step1; decide +kernel
      have hl : raw14202step1Labels = labelEmbedding9 ∘ raw14202step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14202step1 raw14202step1Labels raw14202step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw14203 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14203step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14203step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14203step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14203 raw14203Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw14203 raw14203Labels = mixedMoment B raw14203step0 raw14203step0Labels := by
      have hz : ∀ j, raw14203 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14203step0 = (fun i j => raw14203 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14203step0 raw14203; decide +kernel
      have hl : raw14203step0Labels = raw14203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14203 raw14203Labels permutation265 hz
    mixedMoment B raw14203step0 raw14203step0Labels = mixedMoment B raw14203step1 raw14203step1Labels := by
      have ha : raw14203step1 = (fun i j => raw14203step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14203step1 raw14203step0; decide +kernel
      have hl : raw14203step1Labels = raw14203step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14203step0 raw14203step0Labels permutation35 permutation4
    mixedMoment B raw14203step1 raw14203step1Labels = mixedMoment B raw14203step2 raw14203step2Labels := by
      have ha : raw14203step2 = -raw14203step1 := by apply Matrix.ext; change ∀ i j, raw14203step2 i j = -(raw14203step1 i j); unfold raw14203step2 raw14203step1; decide +kernel
      have hl : raw14203step2Labels = raw14203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14203step2 raw14203step2Labels = mixedMoment B raw14203step3 raw14203step3Labels := by
      have ha : raw14203step3 = raw14203step2 := by apply Matrix.ext; unfold raw14203step3 raw14203step2; decide +kernel
      have hl : raw14203step2Labels = labelEmbedding7 ∘ raw14203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14203step2 raw14203step2Labels raw14203step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw14204 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14204step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14204step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14204 raw14204Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw14204 raw14204Labels = mixedMoment B raw14204step0 raw14204step0Labels := by
      have ha : raw14204step0 = (fun i j => raw14204 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14204step0 raw14204; decide +kernel
      have hl : raw14204step0Labels = raw14204Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14204 raw14204Labels permutation155 permutation6
    mixedMoment B raw14204step0 raw14204step0Labels = mixedMoment B raw14204step1 raw14204step1Labels := by
      have ha : raw14204step1 = raw14204step0 := by apply Matrix.ext; unfold raw14204step1 raw14204step0; decide +kernel
      have hl : raw14204step0Labels = labelEmbedding9 ∘ raw14204step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14204step0 raw14204step0Labels raw14204step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw14205 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14205step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14205step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14205 raw14205Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw14205 raw14205Labels = mixedMoment B raw14205step0 raw14205step0Labels := by
      have hz : ∀ j, raw14205 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14205step0 = (fun i j => raw14205 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14205step0 raw14205; decide +kernel
      have hl : raw14205step0Labels = raw14205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14205 raw14205Labels permutation265 hz
    mixedMoment B raw14205step0 raw14205step0Labels = mixedMoment B raw14205step1 raw14205step1Labels := by
      have ha : raw14205step1 = (fun i j => raw14205step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14205step1 raw14205step0; decide +kernel
      have hl : raw14205step1Labels = raw14205step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14205step0 raw14205step0Labels permutation35 permutation6
    mixedMoment B raw14205step1 raw14205step1Labels = mixedMoment B raw14205step2 raw14205step2Labels := by
      have ha : raw14205step2 = raw14205step1 := by apply Matrix.ext; unfold raw14205step2 raw14205step1; decide +kernel
      have hl : raw14205step1Labels = labelEmbedding9 ∘ raw14205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14205step1 raw14205step1Labels raw14205step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw14206 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14206step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14206step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14206 raw14206Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw14206 raw14206Labels = mixedMoment B raw14206step0 raw14206step0Labels := by
      have hz : ∀ j, raw14206 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14206step0 = (fun i j => raw14206 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14206step0 raw14206; decide +kernel
      have hl : raw14206step0Labels = raw14206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14206 raw14206Labels permutation265 hz
    mixedMoment B raw14206step0 raw14206step0Labels = mixedMoment B raw14206step1 raw14206step1Labels := by
      have ha : raw14206step1 = (fun i j => raw14206step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14206step1 raw14206step0; decide +kernel
      have hl : raw14206step1Labels = raw14206step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14206step0 raw14206step0Labels permutation35 permutation6
    mixedMoment B raw14206step1 raw14206step1Labels = mixedMoment B raw14206step2 raw14206step2Labels := by
      have ha : raw14206step2 = raw14206step1 := by apply Matrix.ext; unfold raw14206step2 raw14206step1; decide +kernel
      have hl : raw14206step1Labels = labelEmbedding9 ∘ raw14206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14206step1 raw14206step1Labels raw14206step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw14207 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14207Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14207 raw14207Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw14207 raw14207Labels = mixedMoment B raw14207step0 raw14207step0Labels := by
      have ha : raw14207step0 = (fun i j => raw14207 (permutation157 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14207step0 raw14207; decide +kernel
      have hl : raw14207step0Labels = raw14207Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14207 raw14207Labels permutation157 permutation6
    _ = mixedMoment B node3074 node3074Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
